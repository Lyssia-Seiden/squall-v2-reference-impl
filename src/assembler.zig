const std = @import("std");
const sq = @import("root.zig");

pub const MatchingRule = @FieldType(sq.DyadicInstr, "matching_rule");
pub const AddrTag = @FieldType(sq.DyadicInstr, "addr_tag");
pub const FormingRuleTag = @FieldType(sq.DyadicInstr, "forming_rule_tag");
pub const FormingRulePayload = @FieldType(sq.DyadicInstr, "forming_rule_payload");

pub const Label = []const u8;
pub const LabelLookup = std.StringHashMap(sq.SqPtr);

pub const Ref = union(enum) {
    node: struct { label: Label, port: sq.Port = .Left },
    halt,

    pub fn l(label: Label) Ref {
        return .{ .node = .{ .label = label, .port = .Left } };
    }
    pub fn r(label: Label) Ref {
        return .{ .node = .{ .label = label, .port = .Right } };
    }

    // pub fn toAddr(self: @This(), labelLookup: LabelLookup) sq.SqPtr {
    //     return switch (self) {
    //         .halt => 0,
    //         .node => labelLookup.get()
    //     };
    // }
};

pub const AddrError = error{
    NoAddrForLabel,
    MisalignedTarget,
    OffsetOutOfRange,
};

/// Distance from `here` to `there` in words, the unit every encoded offset uses.
fn wordDelta(here: sq.SqPtr, there: sq.SqPtr) AddrError!i64 {
    const delta = @as(i64, there) - @as(i64, here);
    if (@rem(delta, @sizeOf(sq.Word)) != 0) return error.MisalignedTarget;
    return @divExact(delta, @sizeOf(sq.Word));
}

fn wordDeltaAs(comptime T: type, here: sq.SqPtr, there: sq.SqPtr) AddrError!T {
    return std.math.cast(T, try wordDelta(here, there)) orelse error.OffsetOutOfRange;
}

fn refDest(ref: Ref, here: sq.SqPtr, labelLookup: LabelLookup) AddrError!sq.Dest {
    return switch (ref) {
        .halt => .{ .offset = try wordDeltaAs(i20, here, 0), .port = .Left },
        .node => |n| .{
            .offset = try wordDeltaAs(
                i20,
                here,
                labelLookup.get(n.label) orelse return error.NoAddrForLabel,
            ),
            .port = n.port,
        },
    };
}

pub const Second = struct { label: Label, port: sq.Port = .Left };

pub const Monadic = struct {
    op: sq.AluOp = .Nop,
    imm: i32 = 0,
    d: Ref,
    second: ?Second = null,
};

pub const Slot = union(enum) {
    frame_words: u11,
    absolute_addr: sq.SqPtr,
    code: Label,

    pub fn toAddrTag(self: @This()) AddrTag {
        return switch (self) {
            .frame_words => .FrameRelative,
            .absolute_addr => .Absolute,
            .code => .CodeRelative,
        };
    }

    pub fn toAddrPayload(
        self: @This(),
        here: sq.SqPtr,
        labelLookup: LabelLookup,
    ) AddrError!u11 {
        return switch (self) {
            .frame_words => |v| v,
            .absolute_addr => |v| blk: {
                if (v % @sizeOf(sq.Word) != 0) return error.MisalignedTarget;
                break :blk std.math.cast(u11, v / @sizeOf(sq.Word)) orelse
                    error.OffsetOutOfRange;
            },
            .code => |v| @bitCast(try wordDeltaAs(
                i11,
                here,
                labelLookup.get(v) orelse return error.NoAddrForLabel,
            )),
        };
    }
};

pub const Form = union(enum) {
    arith: sq.AluOp,
    send,
    extract: Ref,

    pub fn toFormingRuleTag(self: @This()) FormingRuleTag {
        return switch (self) {
            .arith => .Arith,
            .send => .Send,
            .extract => .Extract,
        };
    }
};

pub const Dyadic = struct {
    slot: Slot,
    matching: MatchingRule,
    form: Form,
    d: Ref,
};

pub const Target = union(enum) { label: Label, addr: sq.SqPtr };

pub const Write = struct { target: Target };

pub const AsmField = union(enum) {
    monadic: Monadic,
    dyadic: Dyadic,
    write: Write,
    value: sq.MemValue,
};
pub const Entry = struct {
    label: Label,
    value: AsmField,
};
pub const SqAsm = std.ArrayList(Entry);

fn value_to_word(
    f: AsmField,
    thisAddr: sq.SqPtr,
    labelLookup: LabelLookup,
) !sq.Word {
    return switch (f) {
        .monadic => |data| @bitCast(sq.Instr{ .tag = .Monadic, .data = .{ .monadic = .{
            .alu_op = data.op,
            .d = try refDest(data.d, thisAddr, labelLookup),
            .send_second_token = data.second != null,
            .second_token_port = if (data.second) |s| s.port else .Left,
            .imm = data.imm,
        } } }),
        .dyadic => |data| @bitCast(sq.Instr{
            .tag = .Dyadic,
            .data = .{ .dyadic = .{
                .addr_tag = data.slot.toAddrTag(),
                .addr = try data.slot.toAddrPayload(thisAddr, labelLookup),
                .forming_rule_tag = data.form.toFormingRuleTag(),
                .forming_rule_payload = switch (data.form) {
                    .arith => |a| .{ .arith = .{ .alu_op = a } },
                    .send => .{ .nothing = 0 },
                    .extract => |v| .{ .extract = .{
                        .d2 = try refDest(v, thisAddr, labelLookup),
                    } },
                },
                .d = try refDest(data.d, thisAddr, labelLookup),
                .matching_rule = data.matching,
            } },
        }),
        .write => |data| @bitCast(sq.Instr{
            .tag = .Write,
            .data = .{ .write = .{
                .ptr = try .parse(switch (data.target) {
                    .addr => |a| a,
                    .label => |l| labelLookup.get(l) orelse return error.NoAddrForLabel,
                }),
            } },
        }),
        .value => |data| @bitCast(sq.MemValue{
            .pb = data.pb,
            .val = data.val,
        }),
    };
}

pub const image_base: sq.SqPtr = 0x10;

fn entryAddr(index: usize) sq.SqPtr {
    return image_base + @as(sq.SqPtr, @intCast(index * @sizeOf(sq.Word)));
}

/// Addresses are fixed by position, so a full map is available before any
/// entry is encoded and forward references resolve like backward ones.
fn resolveLabels(allocator: std.mem.Allocator, entries: []const Entry) !LabelLookup {
    var labelLookup: LabelLookup = .init(allocator);
    errdefer labelLookup.deinit();
    for (entries, 0..) |entry, i| {
        const slot = try labelLookup.getOrPut(entry.label);
        if (slot.found_existing) return error.DuplicateLabel;
        slot.value_ptr.* = entryAddr(i);
    }
    return labelLookup;
}

pub fn create_image(
    allocator: std.mem.Allocator,
    entries: []const Entry,
    tokens: []const sq.Token,
    stackBase: sq.SqPtr,
) !sq.State {
    var state: sq.State = .{
        .memory = .init(allocator),
        .stackBase = stackBase,
        .stackTop = stackBase,
    };
    errdefer state.memory.deinit();

    var labelLookup = try resolveLabels(allocator, entries);
    defer labelLookup.deinit();

    for (entries, 0..) |entry, i| {
        const addr = entryAddr(i);
        state.write(sq.Word, addr, try value_to_word(entry.value, addr, labelLookup));
    }

    for (tokens) |token|
        state.push(token);

    return state;
}

test "labels resolve in both directions" {
    const allocator = std.testing.allocator;
    var state = try create_image(allocator, &.{
        .{ .label = "a", .value = .{ .monadic = .{ .d = .l("b") } } },
        .{ .label = "b", .value = .{ .monadic = .{ .d = .l("a") } } },
        .{ .label = "c", .value = .{ .monadic = .{ .d = .halt } } },
    }, &.{}, 0x1000);
    defer state.memory.deinit();

    const word = @sizeOf(sq.Word);
    const a: sq.Instr = @bitCast(state.read(sq.Instr, image_base));
    const b: sq.Instr = @bitCast(state.read(sq.Instr, image_base + word));
    const c: sq.Instr = @bitCast(state.read(sq.Instr, image_base + 2 * word));

    try std.testing.expectEqual(@as(i20, 1), a.data.monadic.d.offset);
    try std.testing.expectEqual(@as(i20, -1), b.data.monadic.d.offset);
    try std.testing.expectEqual(
        -@as(i20, @intCast((image_base + 2 * word) / word)),
        c.data.monadic.d.offset,
    );
}

test "duplicate labels are rejected" {
    try std.testing.expectError(error.DuplicateLabel, create_image(
        std.testing.allocator,
        &.{
            .{ .label = "a", .value = .{ .monadic = .{ .d = .halt } } },
            .{ .label = "a", .value = .{ .monadic = .{ .d = .halt } } },
        },
        &.{},
        0x1000,
    ));
}
