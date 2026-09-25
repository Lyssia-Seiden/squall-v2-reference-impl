const std = @import("std");
const sq = @import("root.zig");
const a = @import("assembler.zig");

const fp_shift = @bitOffsetOf(sq.Tag, "fp");

/// Frame slots of one `fib` activation. Every dyadic instruction that matches
/// two tokens needs a slot of its own.
const FibSlot = enum(u11) {
    pred,
    child_tag,
    arg1,
    ra1,
    arg2,
    ra2,
    join,
    ret,

    fn slot(self: FibSlot) a.Slot {
        return .{ .frame_words = @intFromEnum(self) };
    }
};

const fib_stride_words: u11 = 16;
const fib_sibling: u62 = @as(u62, fib_stride_words) << fp_shift;

comptime {
    std.debug.assert(fib_stride_words >= @typeInfo(FibSlot).@"enum".fields.len);
}

/// Child frames follow binary heap indexing: fp' = 2*fp for the first call and
/// fp' = 2*fp + stride for the second, so every activation in the call tree
/// lands on a distinct frame without an allocator.
const fib_entries = [_]a.Entry{
    .{ .label = "entry_n", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("shift"),
        .second = .{ .label = "sw", .port = .Right },
    } } },
    .{ .label = "sw", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.pred),
        .matching = .Once,
        .form = .{ .arith = .{
            .op = .Beqz,
            .second = .{ .label = "base_ret", .port = .Left },
        } },
        .d = .l("rec_entry"),
    } } },
    .{ .label = "base_ret", .value = .{ .monadic = .{
        .d = .r("final_send"),
    } } },
    .{ .label = "shift", .value = .{ .monadic = .{
        .op = .Shrl,
        .imm = .{ .literal = 1 },
        .d = .l("sw"),
    } } },
    .{ .label = "ret_join", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.join),
        .matching = .Once,
        .form = .{ .arith = .{ .op = .Add } },
        .d = .r("final_send"),
    } } },
    .{ .label = "final_send", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.ret),
        .matching = .Once,
        .form = .send,
        .d = .halt,
    } } },
    .{ .label = "rec_entry", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("decr1"),
        .second = .{ .label = "fan1" },
    } } },
    .{ .label = "fan1", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("decr2"),
        .second = .{ .label = "fan2" },
    } } },
    .{ .label = "fan2", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("ext_fp"),
        .second = .{ .label = "fan3" },
    } } },
    .{ .label = "fan3", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("ext_entry"),
        .second = .{ .label = "fan4" },
    } } },
    .{ .label = "fan4", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("ext_ra1"),
        .second = .{ .label = "ext_ra2" },
    } } },
    .{ .label = "ext_ra2", .value = .{ .dyadic = .{
        .slot = scratch,
        .matching = .Read,
        .form = .{ .extract = .r("ret_join") },
        .d = .r("send_ra2"),
    } } },
    .{ .label = "ext_ra1", .value = .{ .dyadic = .{
        .slot = scratch,
        .matching = .Read,
        .form = .{ .extract = .l("ret_join") },
        .d = .r("send_ra1"),
    } } },
    .{ .label = "ext_fp", .value = .{ .dyadic = .{
        .slot = scratch,
        .matching = .Read,
        .form = .{ .extract = .halt },
        .d = .r("child_tag"),
    } } },
    .{ .label = "ext_entry", .value = .{ .dyadic = .{
        .slot = scratch,
        .matching = .Read,
        .form = .{ .extract = .l("entry_n") },
        .d = .l("child_tag"),
    } } },
    .{ .label = "child_tag", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.child_tag),
        .matching = .Once,
        .form = .{ .arith = .{ .op = .Add } },
        .d = .l("tag1_fan"),
    } } },
    .{ .label = "tag1_fan", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("send_n1"),
        .second = .{ .label = "tag1_fan2" },
    } } },
    .{ .label = "tag1_fan2", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("ra1_tag"),
        .second = .{ .label = "tag2" },
    } } },
    .{ .label = "tag2", .value = .{ .dyadic = .{
        .slot = .{ .code = "sibling" },
        .matching = .Read,
        .form = .{ .arith = .{ .op = .Add } },
        .d = .l("tag2_fan"),
    } } },
    .{ .label = "tag2_fan", .value = .{ .monadic = .{
        .op = .Dupl,
        .d = .l("send_n2"),
        .second = .{ .label = "ra2_tag" },
    } } },
    .{ .label = "ra2_tag", .value = .{ .monadic = .{
        .op = .Add,
        .imm = ret_offset,
        .d = .l("send_ra2"),
    } } },
    .{ .label = "ra1_tag", .value = .{ .monadic = .{
        .op = .Add,
        .imm = ret_offset,
        .d = .l("send_ra1"),
    } } },
    .{ .label = "decr1", .value = .{ .monadic = .{
        .op = .Add,
        .imm = .{ .literal = -1 },
        .d = .r("send_n1"),
    } } },
    .{ .label = "decr2", .value = .{ .monadic = .{
        .op = .Add,
        .imm = .{ .literal = -2 },
        .d = .r("send_n2"),
    } } },
    .{ .label = "send_n1", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.arg1),
        .matching = .Once,
        .form = .send,
        .d = .halt,
    } } },
    .{ .label = "send_ra1", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.ra1),
        .matching = .Once,
        .form = .send,
        .d = .halt,
    } } },
    .{ .label = "send_n2", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.arg2),
        .matching = .Once,
        .form = .send,
        .d = .halt,
    } } },
    .{ .label = "send_ra2", .value = .{ .dyadic = .{
        .slot = FibSlot.slot(.ra2),
        .matching = .Once,
        .form = .send,
        .d = .halt,
    } } },
    .{ .label = "host_return", .value = .{ .write = .{
        .target = .{ .label = "result" },
    } } },
    .{ .label = "result", .value = .{ .value = .{ .pb = .Empty, .val = 0 } } },
    .{ .label = "sibling", .value = .{ .value = .{ .pb = .Constant, .val = fib_sibling } } },
};

const scratch: a.Slot = .{ .absolute_addr = 0 };

const ret_offset: a.Imm = .{ .label_delta = .{ .from = "entry_n", .to = "final_send" } };

/// A program plus the host side of its calling convention: `arg` and `ra` are
/// where the two entry tokens land, `host` is the instruction a returning token
/// hits, and `result` is the word that instruction writes.
///
/// Address space, low to high: image, token stack (grows down from
/// `stack_base`), frame heap (grows up from `root_frame`).
pub const Program = struct {
    name: []const u8,
    entries: []const a.Entry,
    input: sq.Word,
    arg: a.Label,
    ra: a.Label,
    host: a.Label,
    result: a.Label,
    stack_base: sq.SqPtr,
    root_frame: sq.SqPtr,
    frame_stride_words: u11,
    max_cycles: usize,
};

pub const programs = [_]Program{
    .{
        .name = "fib",
        .entries = &fib_entries,
        .input = 10,
        .arg = "entry_n",
        .ra = "final_send",
        .host = "host_return",
        .result = "result",
        .stack_base = 0x800 - @sizeOf(sq.Token),
        .root_frame = 0x800,
        .frame_stride_words = fib_stride_words,
        .max_cycles = 1 << 22,
    },
};

pub const Error = error{
    UnknownProgram,
    FrameOverlapsStack,
    FrameNotStrideAligned,
    RootFrameIndexTooLow,
    StackOverlapsImage,
    TokenStackOverflow,
    ImageClobbered,
};

fn labelAddr(labels: a.LabelLookup, label: a.Label) !sq.SqPtr {
    return labels.get(label) orelse error.NoAddrForLabel;
}

fn entryTokens(p: Program, labels: a.LabelLookup) ![2]sq.Token {
    const fp: sq.AlignedSqPtr(3) = try .parse(p.root_frame);
    const host: sq.Tag = .init(
        try .parse(try labelAddr(labels, p.host)),
        try .parse(0),
        .Left,
    );
    return .{
        .{
            .tag = .init(try .parse(try labelAddr(labels, p.ra)), fp, .Left),
            .acc = @as(sq.EffWord, @bitCast(host)),
        },
        .{
            .tag = .init(try .parse(try labelAddr(labels, p.arg)), fp, .Left),
            .acc = p.input,
        },
    };
}

fn imageEnd(p: Program) sq.SqPtr {
    return a.image_base + @as(sq.SqPtr, @intCast(p.entries.len * @sizeOf(sq.Word)));
}

fn checkLayout(p: Program) Error!void {
    const stride = @as(sq.SqPtr, p.frame_stride_words) * @sizeOf(sq.Word);
    if (p.root_frame % stride != 0) return error.FrameNotStrideAligned;
    if (p.root_frame / stride < 1) return error.RootFrameIndexTooLow;
    if (p.stack_base + @sizeOf(sq.Token) > p.root_frame) return error.FrameOverlapsStack;
    if (p.stack_base < imageEnd(p)) return error.StackOverlapsImage;
}

/// Deepest activation whose frame pointer still fits the tag's fp field.
fn maxDepth(p: Program) usize {
    const limit = (1 << @typeInfo(sq.SqPtr).int.bits) - @sizeOf(sq.Word);
    return std.math.log2_int(u64, limit / p.root_frame);
}

const Trace = struct { cycles: usize, peak_stack: sq.SqPtr };

fn run(state: *sq.State, max_cycles: usize) Trace {
    var trace: Trace = .{ .cycles = 0, .peak_stack = 0 };
    while (trace.cycles < max_cycles and !state.quiescent()) : (trace.cycles += 1) {
        sq.clock(state);
        const used = state.stackBase - state.stackTop;
        if (used > trace.peak_stack) trace.peak_stack = used;
    }
    return trace;
}

fn readWord(state: *const sq.State, addr: sq.SqPtr) sq.Word {
    return @bitCast(state.read(sq.Word, addr));
}

/// A wrapped frame pointer, a token stack overrun or a stray `Write` all land in
/// the image, so comparing it against the pristine copy catches them.
fn checkImage(
    p: Program,
    image: *const sq.State,
    sim: *const sq.State,
    result_addr: sq.SqPtr,
) Error!void {
    var addr = a.image_base;
    while (addr < imageEnd(p)) : (addr += @sizeOf(sq.Word)) {
        if (addr == result_addr) continue;
        if (readWord(image, addr) != readWord(sim, addr)) return error.ImageClobbered;
    }
}

fn memoryHex(gpa: std.mem.Allocator, state: *const sq.State) ![]u8 {
    var words: std.ArrayList(sq.SqPtr) = .empty;
    defer words.deinit(gpa);

    var keys = state.memory.keyIterator();
    while (keys.next()) |key| {
        try words.append(gpa, key.* & ~@as(sq.SqPtr, @sizeOf(sq.Word) - 1));
    }
    std.mem.sort(sq.SqPtr, words.items, {}, std.sort.asc(sq.SqPtr));

    var out: std.Io.Writer.Allocating = .init(gpa);
    errdefer out.deinit();
    var last: ?sq.SqPtr = null;
    for (words.items) |addr| {
        if (last != null and last.? == addr) continue;
        last = addr;
        try out.writer.print("@{x} {x}\n", .{
            addr / @sizeOf(sq.Word),
            readWord(state, addr),
        });
    }
    return out.toOwnedSlice();
}

pub const Report = struct {
    cycles: usize,
    peak_stack: sq.SqPtr,
    /// Highest byte the run touched; how much memory a dense simulation needs.
    high_addr: sq.SqPtr,
    quiescent: bool,
    result: sq.Word,
};

fn highAddr(state: *const sq.State) sq.SqPtr {
    var high: sq.SqPtr = 0;
    var keys = state.memory.keyIterator();
    while (keys.next()) |key| high = @max(high, key.*);
    return high;
}

pub fn exportProgram(
    gpa: std.mem.Allocator,
    io: std.Io,
    out_root: []const u8,
    p: Program,
) !Report {
    try checkLayout(p);

    var labels = try a.resolveLabels(gpa, p.entries);
    defer labels.deinit();

    const tokens = try entryTokens(p, labels);

    var image = try a.create_image(gpa, p.entries, &tokens, p.stack_base);
    defer image.memory.deinit();

    var sim = try a.create_image(gpa, p.entries, &tokens, p.stack_base);
    defer sim.memory.deinit();

    const trace = run(&sim, p.max_cycles);
    if (p.stack_base - trace.peak_stack < imageEnd(p)) return error.TokenStackOverflow;

    const result_addr = try labelAddr(labels, p.result);
    try checkImage(p, &image, &sim, result_addr);
    const report: Report = .{
        .cycles = trace.cycles,
        .peak_stack = trace.peak_stack,
        .high_addr = highAddr(&sim),
        .quiescent = sim.quiescent(),
        .result = readWord(&sim, result_addr),
    };

    const memory = try memoryHex(gpa, &image);
    defer gpa.free(memory);

    var params: std.Io.Writer.Allocating = .init(gpa);
    defer params.deinit();
    try params.writer.print(
        \\program = {s}
        \\input = {d}
        \\num_tokens = {d}
        \\token_bytes = {d}
        \\word_bytes = {d}
        \\image_base = 0x{x}
        \\image_end = 0x{x}
        \\stack_base = 0x{x}
        \\stack_top = 0x{x}
        \\root_frame = 0x{x}
        \\frame_stride_words = {d}
        \\max_depth = {d}
        \\result_word = 0x{x}
        \\expected_result = 0x{x}
        \\cycles = {d}
        \\quiescent = {}
        \\max_cycles = {d}
        \\peak_stack_bytes = 0x{x}
        \\high_addr = 0x{x}
        \\
    , .{
        p.name,
        p.input,
        tokens.len,
        @sizeOf(sq.Token),
        @sizeOf(sq.Word),
        a.image_base,
        imageEnd(p),
        p.stack_base,
        image.stackTop,
        p.root_frame,
        p.frame_stride_words,
        maxDepth(p),
        result_addr / @sizeOf(sq.Word),
        report.result,
        report.cycles,
        report.quiescent,
        p.max_cycles,
        report.peak_stack,
        report.high_addr,
    });

    const dir_path = try std.fs.path.join(gpa, &.{ out_root, p.name });
    defer gpa.free(dir_path);
    var dir = try std.Io.Dir.cwd().createDirPathOpen(io, dir_path, .{});
    defer dir.close(io);

    try dir.writeFile(io, .{ .sub_path = "memory.hex", .data = memory });
    try dir.writeFile(io, .{ .sub_path = "params.txt", .data = params.written() });

    return report;
}

pub fn main(init: std.process.Init) !void {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    const out_root = if (args.len > 1) args[1] else "out";

    for (programs) |program| {
        var p = program;
        if (args.len > 2) p.input = try std.fmt.parseInt(sq.Word, args[2], 10);

        const report = try exportProgram(init.gpa, init.io, out_root, p);
        std.debug.print("{s}({d}) -> 0x{x} in {d} cycles{s}\n", .{
            p.name,
            p.input,
            report.result,
            report.cycles,
            if (report.quiescent) "" else " (cycle cap hit)",
        });
    }
}

test "fib matches a reference implementation" {
    const gpa = std.testing.allocator;
    var labels = try a.resolveLabels(gpa, &fib_entries);
    defer labels.deinit();

    var p = programs[0];
    try checkLayout(p);
    for (0..13) |n| {
        p.input = n;
        const tokens = try entryTokens(p, labels);
        var sim = try a.create_image(gpa, p.entries, &tokens, p.stack_base);
        defer sim.memory.deinit();

        const trace = run(&sim, p.max_cycles);
        try std.testing.expect(sim.quiescent());
        try std.testing.expect(p.stack_base - trace.peak_stack >= imageEnd(p));
        try std.testing.expectEqual(
            fibReference(n),
            readWord(&sim, try labelAddr(labels, p.result)),
        );
    }
}

fn fibReference(n: usize) sq.Word {
    var prev: sq.Word = 0;
    var cur: sq.Word = 1;
    if (n == 0) return 0;
    for (1..n) |_| {
        const next = prev + cur;
        prev = cur;
        cur = next;
    }
    return cur;
}
