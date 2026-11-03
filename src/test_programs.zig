//! Design-verification programs for checking the RTL against this model.
//!
//! Every program here follows the same host calling convention as `fib`
//! (see `programs.Program`), so the RTL testbench loads them the same way.
//! On top of the single `result` word, each program declares *check words*:
//! intermediate values that a `Write` instruction stores to the image as the
//! program runs. When the RTL disagrees with the model, the first failing
//! check names the instruction that went wrong instead of just "wrong answer".
//!
//! Every check write is acked into the token flow that produces `result`,
//! so all checks are written before the result is; a testbench that stops
//! on the result write still sees every check.
//!
//! Each directed check carries a hand-computed expectation written with
//! plain Zig arithmetic (not `apply_alu`), so `zig build test` also checks
//! the model against the ISA's intended semantics. Random programs only
//! carry the model's own answer.
//!
//! Programs avoid schedule-dependent behaviour: every matching slot sees its
//! tokens in an order fixed by data dependencies, so an RTL that schedules
//! tokens differently from the model's LIFO stack must still match.

const std = @import("std");
const sq = @import("root.zig");
const a = @import("assembler.zig");
const P = @import("programs.zig");

const Word = sq.Word;
const Ref = a.Ref;
const Label = a.Label;

/// All test programs share one layout so absolute addresses (frame writes,
/// absolute reads) are known while the image is built.
pub const root_frame: sq.SqPtr = 0x4000;
const stack_base: sq.SqPtr = root_frame - @sizeOf(sq.Token);
/// Stride covers one presence-bit group; only the call test uses a second frame.
const frame_stride_words: u11 = 32;
const fp_shift = @bitOffsetOf(sq.Tag, "fp");

/// Written into every check word in the image so a check the RTL never
/// wrote can't pass by accident.
pub const sentinel: Word = 0xBAD0_BAD0_BAD0_BAD0;

fn sx(v: i32) Word {
    return @bitCast(@as(i64, v));
}
fn s(v: Word) i64 {
    return @bitCast(v);
}
fn u(v: i64) Word {
    return @bitCast(v);
}

pub const Builder = struct {
    arena: std.mem.Allocator,
    entries: std.ArrayList(a.Entry) = .empty,
    checks: std.ArrayList(P.Check) = .empty,
    next_frame_word: u11 = 1,

    pub fn init(arena: std.mem.Allocator) Builder {
        return .{ .arena = arena };
    }

    pub fn lbl(b: *Builder, comptime fmt: []const u8, args: anytype) Label {
        return std.fmt.allocPrint(b.arena, fmt, args) catch @panic("OOM");
    }

    /// Appends an entry. The word after the last slot of each 32-word group is
    /// that next group's presence-bit word, so an instruction with a second
    /// output must not sit in that last slot; a pad word is inserted to push
    /// it into the next group.
    pub fn add(b: *Builder, label: Label, value: a.AsmField) void {
        if (secondOf(value) != null and b.atGroupEnd()) {
            if (b.entries.items.len > 0) {
                if (secondOf(b.entries.items[b.entries.items.len - 1].value)) |prev| {
                    if (std.mem.eql(u8, prev, label))
                        std.debug.panic("chain of second outputs straddles a presence-bit word at {s}", .{label});
                }
            }
            b.addRaw(b.lbl("pad{d}", .{b.entries.items.len}), .{ .value = .{ .val = 0 } });
        }
        b.addRaw(label, value);
    }

    fn addRaw(b: *Builder, label: Label, value: a.AsmField) void {
        b.entries.append(b.arena, .{ .label = label, .value = value }) catch @panic("OOM");
    }

    /// The next entry would be the last data word of its presence-bit group.
    fn atGroupEnd(b: *const Builder) bool {
        return sq.pb_slot_for(a.entryAddr(b.entries.items.len)) == sq.pb_group_words - 1;
    }

    fn secondOf(value: a.AsmField) ?Label {
        return switch (value) {
            .monadic => |m| if (m.second) |sec| sec.label else null,
            .dyadic => |d| switch (d.form) {
                .arith => |ar| if (ar.second) |sec| sec.label else null,
                .send => null,
            },
            else => null,
        };
    }

    /// Address `label` will have; only valid for entries already added.
    pub fn addrOf(b: *const Builder, label: Label) sq.SqPtr {
        for (b.entries.items, 0..) |e, i| {
            if (std.mem.eql(u8, e.label, label)) return a.entryAddr(i);
        }
        @panic("addrOf: label not added yet");
    }

    /// A fresh frame-relative slot, skipping the presence-bit word that
    /// starts each 32-word group.
    pub fn frame(b: *Builder) a.Slot {
        if (b.next_frame_word % sq.pb_group_words == 0) b.next_frame_word += 1;
        defer b.next_frame_word += 1;
        return .{ .frame_words = b.next_frame_word };
    }

    /// Emits `<name>: write chk_<name>` (acking into `ack`) followed by the
    /// check word. Returns the write instruction's label. The write is
    /// emitted first so callers can place it at `ip + 1` of a two-output op.
    pub fn probe(b: *Builder, name: []const u8, expected: ?Word, ack: Ref) Label {
        const w = b.lbl("w_{s}", .{name});
        const c = b.lbl("chk_{s}", .{name});
        b.add(w, .{ .write = .{ .target = .{ .label = c }, .ack = ack } });
        b.add(c, .{ .value = .{ .val = sentinel } });
        b.checks.append(b.arena, .{ .label = c, .expected = expected }) catch @panic("OOM");
        return w;
    }

    /// A chain of `Dupl` instructions handing one copy of the incoming token
    /// to each of `dests`, each passing the token on to the next at `ip + 1`.
    /// Where the chain reaches the end of a presence-bit group, a `Nop` hop
    /// carries it over the presence-bit word. Returns the chain's entry label.
    pub fn fanout(b: *Builder, base: []const u8, dests: []const Ref) Label {
        std.debug.assert(dests.len > 0);
        for (dests, 0..) |d, i| {
            const last = i + 1 == dests.len;
            var label = b.lbl("{s}_fan{d}", .{ base, i });
            if (!last and b.atGroupEnd()) {
                const cont = b.lbl("{s}_fan{d}_c", .{ base, i });
                b.add(label, .{ .monadic = .{ .d = .l(cont) } });
                label = cont;
            }
            b.add(label, .{ .monadic = .{
                .op = if (last) .Nop else .Dupl,
                .d = d,
                .second = if (last) null else .{ .label = b.lbl("{s}_fan{d}", .{ base, i + 1 }) },
            } });
        }
        return b.lbl("{s}_fan0", .{base});
    }

    /// The standard tail: the ra token and the final value meet at
    /// `final_send`, which sends the value to the host's `Write`.
    pub fn harness(b: *Builder) void {
        b.add("final_send", .{ .dyadic = .{
            .slot = b.frame(),
            .matching = .Once,
            .form = .send,
            .d = .halt,
        } });
        b.add("host_return", .{ .write = .{ .target = .{ .label = "result" } } });
        b.add("result", .{ .value = .{ .val = sentinel } });
    }

    pub fn finish(
        b: *Builder,
        name: []const u8,
        arg: Label,
        input: Word,
        expected_result: ?Word,
        fixed_input: bool,
        max_cycles: usize,
    ) P.Program {
        return .{
            .name = name,
            .entries = b.entries.items,
            .input = input,
            .arg = arg,
            .ra = "final_send",
            .host = "host_return",
            .result = "result",
            .stack_base = stack_base,
            .root_frame = root_frame,
            .frame_stride_words = frame_stride_words,
            .max_cycles = max_cycles,
            .checks = b.checks.items,
            .expected_result = expected_result,
            .fixed_input = fixed_input,
        };
    }
};

/// Collects `n` tokens into one with a chain of dyadic joins, one frame slot
/// each. Input 0 enters join 1 on the left; input k enters join k on the
/// right. Joins fire in a data-dependent order, so the chain is
/// schedule-independent.
const Joiner = struct {
    base: []const u8,
    n: usize,
    out: Ref,
    op: sq.AluOp,

    fn name(j: Joiner, b: *Builder, k: usize) Label {
        return b.lbl("{s}_join{d}", .{ j.base, k });
    }

    fn in(j: Joiner, b: *Builder, k: usize) Ref {
        std.debug.assert(k < j.n);
        if (j.n == 1) return j.out;
        if (k == 0) return .l(j.name(b, 1));
        return .r(j.name(b, k));
    }

    fn emit(j: Joiner, b: *Builder) void {
        for (1..j.n) |k| {
            b.add(j.name(b, k), .{ .dyadic = .{
                .slot = b.frame(),
                .matching = .Once,
                .form = .{ .arith = .{ .op = j.op } },
                .d = if (k + 1 == j.n) j.out else .l(j.name(b, k + 1)),
            } });
        }
    }

    /// What the chain computes from its inputs, for the expected result.
    fn fold(j: Joiner, vals: []const Word) Word {
        var acc = vals[0];
        for (vals[1..]) |v| acc = switch (j.op) {
            .Xor => acc ^ v,
            .Add => acc +% v,
            else => unreachable,
        };
        return acc;
    }
};

// ---------------------------------------------------------------------------
// alu_imm: every monadic ALU op against an immediate, token on both ports.
// ---------------------------------------------------------------------------

const ImmCase = struct {
    name: []const u8,
    op: sq.AluOp,
    imm: i32,
    port: sq.Port,
    expect: Word,
};

const X: Word = 0xF0E1_D2C3_B4A5_9687; // negative as i64, low 6 bits = 7

const alu_imm_cases = [_]ImmCase{
    // token on the left: (acc OP imm)
    .{ .name = "nop_l", .op = .Nop, .imm = 5, .port = .Left, .expect = X },
    .{ .name = "add_l", .op = .Add, .imm = 0x1234, .port = .Left, .expect = X +% 0x1234 },
    .{ .name = "add_neg_l", .op = .Add, .imm = -1, .port = .Left, .expect = X -% 1 },
    .{ .name = "sub_l", .op = .Sub, .imm = 0x7FFF_FFFF, .port = .Left, .expect = X -% 0x7FFF_FFFF },
    .{ .name = "mul_l", .op = .Mul, .imm = -3, .port = .Left, .expect = X *% sx(-3) },
    .{ .name = "div_l", .op = .Div, .imm = 7, .port = .Left, .expect = u(@divTrunc(s(X), 7)) },
    .{ .name = "div_neg_l", .op = .Div, .imm = -7, .port = .Left, .expect = u(@divTrunc(s(X), -7)) },
    .{ .name = "divu_l", .op = .Divu, .imm = 7, .port = .Left, .expect = X / 7 },
    .{ .name = "rem_l", .op = .Rem, .imm = 7, .port = .Left, .expect = u(@rem(s(X), 7)) },
    .{ .name = "rem_neg_l", .op = .Rem, .imm = -7, .port = .Left, .expect = u(@rem(s(X), -7)) },
    .{ .name = "mod_l", .op = .Mod, .imm = 7, .port = .Left, .expect = u(@mod(s(X), 7)) },
    .{ .name = "mod_neg_l", .op = .Mod, .imm = -7, .port = .Left, .expect = u(@mod(s(X), -7)) },
    .{ .name = "and_l", .op = .And, .imm = 0x0F0F_0F0F, .port = .Left, .expect = X & 0x0F0F_0F0F },
    .{ .name = "and_neg_l", .op = .And, .imm = -256, .port = .Left, .expect = X & sx(-256) },
    .{ .name = "or_l", .op = .Or, .imm = std.math.minInt(i32), .port = .Left, .expect = X | 0xFFFF_FFFF_8000_0000 },
    .{ .name = "xor_l", .op = .Xor, .imm = -1, .port = .Left, .expect = ~X },
    .{ .name = "shl_l", .op = .Shl, .imm = 4, .port = .Left, .expect = X << 4 },
    .{ .name = "shl_wrap_l", .op = .Shl, .imm = 68, .port = .Left, .expect = X << 4 }, // amount is mod 64
    .{ .name = "shrl_l", .op = .Shrl, .imm = 8, .port = .Left, .expect = X >> 8 },
    .{ .name = "shra_l", .op = .Shra, .imm = 8, .port = .Left, .expect = u(s(X) >> 8) },
    .{ .name = "shra63_l", .op = .Shra, .imm = 63, .port = .Left, .expect = ~@as(Word, 0) },
    .{ .name = "not_l", .op = .Not, .imm = 0, .port = .Left, .expect = ~X },
    .{ .name = "rev_l", .op = .Rev, .imm = 0, .port = .Left, .expect = @bitReverse(X) },
    .{ .name = "dupl_l", .op = .Dupl, .imm = 9, .port = .Left, .expect = X },
    .{ .name = "dupr_l", .op = .Dupr, .imm = 9, .port = .Left, .expect = 9 },
    // token on the right: (imm OP acc)
    .{ .name = "nop_r", .op = .Nop, .imm = -5, .port = .Right, .expect = sx(-5) },
    .{ .name = "sub_r", .op = .Sub, .imm = 100, .port = .Right, .expect = 100 -% X },
    .{ .name = "div_r", .op = .Div, .imm = 0x7FFF_FFFF, .port = .Right, .expect = u(@divTrunc(0x7FFF_FFFF, s(X))) },
    .{ .name = "divu_r", .op = .Divu, .imm = -1, .port = .Right, .expect = ~@as(Word, 0) / X },
    .{ .name = "rem_r", .op = .Rem, .imm = 1000, .port = .Right, .expect = u(@rem(@as(i64, 1000), s(X))) },
    .{ .name = "mod_r", .op = .Mod, .imm = 1000, .port = .Right, .expect = u(@mod(@as(i64, 1000), s(X))) },
    .{ .name = "shl_r", .op = .Shl, .imm = 1, .port = .Right, .expect = 1 << 7 },
    .{ .name = "shrl_r", .op = .Shrl, .imm = -1, .port = .Right, .expect = ~@as(Word, 0) >> 7 },
    .{ .name = "shra_r", .op = .Shra, .imm = std.math.minInt(i32), .port = .Right, .expect = u(@as(i64, std.math.minInt(i32)) >> 7) },
    .{ .name = "not_r", .op = .Not, .imm = 0x55, .port = .Right, .expect = ~@as(Word, 0x55) },
    .{ .name = "dupl_r", .op = .Dupl, .imm = 77, .port = .Right, .expect = 77 },
    .{ .name = "dupr_r", .op = .Dupr, .imm = 77, .port = .Right, .expect = X },
};

fn aluImm(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const n = alu_imm_cases.len;
    const j: Joiner = .{ .base = "alu", .n = n, .out = .r("final_send"), .op = .Xor };

    var dests: [n]Ref = undefined;
    for (alu_imm_cases, 0..) |c, i| dests[i] = .{ .node = .{ .label = c.name, .port = c.port } };
    const entry = b.fanout("x", &dests);

    var vals: [n]Word = undefined;
    for (alu_imm_cases, 0..) |c, i| {
        vals[i] = c.expect;
        b.add(c.name, .{ .monadic = .{
            .op = c.op,
            .imm = .{ .literal = c.imm },
            .d = .l(b.lbl("w_{s}", .{c.name})),
        } });
        _ = b.probe(c.name, c.expect, j.in(&b, i));
    }
    j.emit(&b);
    b.harness();
    return b.finish("alu_imm", entry, X, j.fold(&vals), true, 1 << 16);
}

// ---------------------------------------------------------------------------
// alu_second: the second output of two-output ops (carry, high word, flags).
// ---------------------------------------------------------------------------

const SecondCase = struct {
    name: []const u8,
    op: sq.AluOp,
    imm: i32,
    port: sq.Port,
    first: Word,
    second: Word,
    second_port: sq.Port = .Left,
};

fn divFlags(zero: bool, trunc: bool) Word {
    return @as(Word, @intFromBool(zero)) | (@as(Word, @intFromBool(trunc)) << 1);
}

const alu_second_cases = [_]SecondCase{
    .{ .name = "add_carry", .op = .Add, .imm = -1, .port = .Left, .first = X -% 1, .second = 1 },
    .{ .name = "add_nocarry", .op = .Add, .imm = 1, .port = .Left, .first = X +% 1, .second = 0 },
    .{ .name = "sub_borrow", .op = .Sub, .imm = 5, .port = .Right, .first = 5 -% X, .second = 1 },
    .{ .name = "sub_noborrow", .op = .Sub, .imm = 5, .port = .Left, .first = X -% 5, .second = 0 },
    .{ .name = "mul_hi", .op = .Mul, .imm = -1, .port = .Left, .first = X *% sx(-1), .second = @truncate((@as(u128, X) * @as(u128, sx(-1))) >> 64) },
    .{ .name = "mul_hi_small", .op = .Mul, .imm = 0x10, .port = .Right, .first = X << 4, .second = X >> 60, .second_port = .Right },
    .{ .name = "div_exact", .op = .Div, .imm = 1, .port = .Left, .first = X, .second = divFlags(false, false) },
    .{ .name = "div_trunc", .op = .Div, .imm = 7, .port = .Left, .first = u(@divTrunc(s(X), 7)), .second = divFlags(false, @rem(s(X), 7) != 0) },
    .{ .name = "div_zero", .op = .Div, .imm = 0, .port = .Left, .first = 0, .second = divFlags(true, false) },
    .{ .name = "divu_zero", .op = .Divu, .imm = 0, .port = .Left, .first = 0, .second = divFlags(true, false) },
    .{ .name = "divu_trunc", .op = .Divu, .imm = 1000, .port = .Right, .first = 0, .second = divFlags(false, true) },
    .{ .name = "rem_zero", .op = .Rem, .imm = 0, .port = .Left, .first = 0, .second = 1 },
    .{ .name = "mod_ok", .op = .Mod, .imm = 3, .port = .Left, .first = u(@mod(s(X), 3)), .second = 0 },
    .{ .name = "not_both", .op = .Not, .imm = 0x0F, .port = .Left, .first = ~X, .second = ~@as(Word, 0x0F) },
    .{ .name = "rev_both", .op = .Rev, .imm = 1, .port = .Left, .first = @bitReverse(X), .second = @as(Word, 1) << 63 },
    .{ .name = "dupl_both", .op = .Dupl, .imm = 3, .port = .Left, .first = X, .second = X },
    .{ .name = "dupr_both", .op = .Dupr, .imm = 3, .port = .Left, .first = 3, .second = 3 },
    .{ .name = "nop_both", .op = .Nop, .imm = 3, .port = .Right, .first = 3, .second = X, .second_port = .Right },
};

fn aluSecond(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const n = alu_second_cases.len;
    const j: Joiner = .{ .base = "sec", .n = 2 * n, .out = .r("final_send"), .op = .Xor };

    var dests: [n]Ref = undefined;
    for (alu_second_cases, 0..) |c, i| dests[i] = .{ .node = .{ .label = c.name, .port = c.port } };
    const entry = b.fanout("x", &dests);

    var vals: [2 * n]Word = undefined;
    for (alu_second_cases, 0..) |c, i| {
        vals[2 * i] = c.first;
        vals[2 * i + 1] = c.second;
        const second_probe = b.lbl("{s}_hi", .{c.name});
        b.add(c.name, .{ .monadic = .{
            .op = c.op,
            .imm = .{ .literal = c.imm },
            .d = .l(b.lbl("w_{s}", .{c.name})),
            .second = .{ .label = b.lbl("w_{s}", .{second_probe}), .port = c.second_port },
        } });
        // must sit at ip + 1 of the op
        _ = b.probe(second_probe, c.second, j.in(&b, 2 * i + 1));
        _ = b.probe(c.name, c.first, j.in(&b, 2 * i));
    }
    j.emit(&b);
    b.harness();
    return b.finish("alu_second", entry, X, j.fold(&vals), true, 1 << 16);
}

// ---------------------------------------------------------------------------
// branch_imm: monadic switch ops, both directions of each.
// The left (d) path adds 0x1000, the right (second) path adds 0x2000, so the
// check word shows which way the token went.
// ---------------------------------------------------------------------------

const BranchCase = struct {
    name: []const u8,
    op: sq.AluOp,
    imm: i32,
    port: sq.Port,
    /// value that comes out, before the path marker
    value: Word,
    taken_right: bool,
};

const B_IN: Word = 42;

const branch_cases = [_]BranchCase{
    .{ .name = "beqz_nz", .op = .Beqz, .imm = 7, .port = .Left, .value = 7, .taken_right = false },
    .{ .name = "beqz_z", .op = .Beqz, .imm = 0, .port = .Right, .value = B_IN, .taken_right = true },
    .{ .name = "beqz_imm_nz", .op = .Beqz, .imm = 5, .port = .Right, .value = B_IN, .taken_right = false },
    .{ .name = "beql_eq", .op = .Beql, .imm = 42, .port = .Left, .value = B_IN, .taken_right = true },
    .{ .name = "beql_ne", .op = .Beql, .imm = 41, .port = .Left, .value = B_IN, .taken_right = false },
    .{ .name = "beqr_eq", .op = .Beqr, .imm = 42, .port = .Left, .value = 42, .taken_right = true },
    .{ .name = "beqr_ne", .op = .Beqr, .imm = 43, .port = .Left, .value = 43, .taken_right = false },
    .{ .name = "blel_eq", .op = .Blel, .imm = 42, .port = .Left, .value = B_IN, .taken_right = false },
    .{ .name = "blel_gt", .op = .Blel, .imm = 41, .port = .Left, .value = B_IN, .taken_right = true },
    // unsigned compare: 42 <= 0xFFFF_FFFF_FFFF_FFFF
    .{ .name = "blel_unsigned", .op = .Blel, .imm = -1, .port = .Left, .value = B_IN, .taken_right = false },
    .{ .name = "bler_le", .op = .Bler, .imm = 100, .port = .Left, .value = 100, .taken_right = false },
    .{ .name = "bler_gt", .op = .Bler, .imm = 100, .port = .Right, .value = B_IN, .taken_right = true },
    // unsigned: 0xFFFF...FFFF (imm) > 42
    .{ .name = "bler_unsigned", .op = .Bler, .imm = -1, .port = .Right, .value = B_IN, .taken_right = true },
};

fn branchImm(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const n = branch_cases.len;
    const j: Joiner = .{ .base = "br", .n = n, .out = .r("final_send"), .op = .Xor };

    var dests: [n]Ref = undefined;
    for (branch_cases, 0..) |c, i| dests[i] = .{ .node = .{ .label = c.name, .port = c.port } };
    const entry = b.fanout("x", &dests);

    var vals: [n]Word = undefined;
    for (branch_cases, 0..) |c, i| {
        const out = c.value +% @as(Word, if (c.taken_right) 0x2000 else 0x1000);
        vals[i] = out;
        const w = b.lbl("w_{s}", .{c.name});
        b.add(c.name, .{ .monadic = .{
            .op = c.op,
            .imm = .{ .literal = c.imm },
            .d = .l(b.lbl("{s}_pl", .{c.name})),
            .second = .{ .label = b.lbl("{s}_pr", .{c.name}) },
        } });
        b.add(b.lbl("{s}_pr", .{c.name}), .{ .monadic = .{ .op = .Add, .imm = .{ .literal = 0x2000 }, .d = .l(w) } });
        b.add(b.lbl("{s}_pl", .{c.name}), .{ .monadic = .{ .op = .Add, .imm = .{ .literal = 0x1000 }, .d = .l(w) } });
        _ = b.probe(c.name, out, j.in(&b, i));
    }
    j.emit(&b);
    b.harness();
    return b.finish("branch_imm", entry, B_IN, j.fold(&vals), true, 1 << 16);
}

// ---------------------------------------------------------------------------
// alu_dyadic: two runtime operands meeting in a frame slot.
// Each case shapes the left and right operand from X with a monadic op, then
// combines them with a dyadic op (optionally with a second output, or a
// branch with marked paths).
// ---------------------------------------------------------------------------

const Shape = struct { op: sq.AluOp = .Nop, imm: i32 = 0 };

const DyCase = struct {
    name: []const u8,
    op: sq.AluOp,
    l: Shape = .{},
    r: Shape = .{},
    first: Word,
    /// two-output op: second output value (sent to ip + 1, left port)
    second: ?Word = null,
    /// switch op: which way it goes (value is `first` + marker)
    branch: ?bool = null,
};

const X_LO8: Word = X & 0xFF; // 0x87
const X_REV: Word = @bitReverse(X);

const dy_cases = [_]DyCase{
    .{ .name = "add", .op = .Add, .r = .{ .op = .Shrl, .imm = 4 }, .first = X +% (X >> 4), .second = @intFromBool(@addWithOverflow(X, X >> 4)[1] == 1) },
    .{ .name = "add_self", .op = .Add, .first = X +% X, .second = 1 },
    .{ .name = "sub", .op = .Sub, .r = .{ .op = .Shrl, .imm = 4 }, .first = X -% (X >> 4), .second = 0 },
    .{ .name = "sub_rev", .op = .Sub, .l = .{ .op = .Shrl, .imm = 4 }, .first = (X >> 4) -% X, .second = 1 },
    .{ .name = "mul", .op = .Mul, .r = .{ .op = .And, .imm = 0xFFFF }, .first = X *% (X & 0xFFFF), .second = @truncate((@as(u128, X) * (X & 0xFFFF)) >> 64) },
    .{ .name = "div", .op = .Div, .r = .{ .op = .And, .imm = 0xFF }, .first = u(@divTrunc(s(X), @as(i64, X_LO8))), .second = divFlags(false, @rem(s(X), @as(i64, X_LO8)) != 0) },
    .{ .name = "div_zero", .op = .Div, .r = .{ .op = .And, .imm = 0 }, .first = 0, .second = divFlags(true, false) },
    .{ .name = "div_neg1", .op = .Div, .r = .{ .op = .Shra, .imm = 60 }, .first = 0 -% X, .second = 0 },
    .{ .name = "divu", .op = .Divu, .r = .{ .op = .And, .imm = 0xFF }, .first = X / X_LO8 },
    .{ .name = "rem", .op = .Rem, .r = .{ .op = .And, .imm = 0xFF }, .first = u(@rem(s(X), @as(i64, X_LO8))) },
    .{ .name = "mod", .op = .Mod, .l = .{ .op = .And, .imm = 0xFF }, .first = u(@mod(@as(i64, X_LO8), s(X))) },
    .{ .name = "and", .op = .And, .r = .{ .op = .Rev }, .first = X & X_REV },
    .{ .name = "or", .op = .Or, .r = .{ .op = .Rev }, .first = X | X_REV },
    .{ .name = "xor", .op = .Xor, .r = .{ .op = .Rev }, .first = X ^ X_REV },
    .{ .name = "shl", .op = .Shl, .r = .{ .op = .Shrl, .imm = 58 }, .first = X << @truncate(X >> 58) },
    .{ .name = "shrl", .op = .Shrl, .r = .{ .op = .Shrl, .imm = 58 }, .first = X >> @truncate(X >> 58) },
    .{ .name = "shra", .op = .Shra, .r = .{ .op = .Shrl, .imm = 58 }, .first = u(s(X) >> @truncate(X >> 58)) },
    .{ .name = "dupl", .op = .Dupl, .r = .{ .op = .Rev }, .first = X },
    .{ .name = "dupr", .op = .Dupr, .r = .{ .op = .Rev }, .first = X_REV },
    .{ .name = "nop2", .op = .Nop, .r = .{ .op = .Rev }, .first = X, .second = X_REV },
    .{ .name = "not2", .op = .Not, .r = .{ .op = .Rev }, .first = ~X, .second = ~X_REV },
    .{ .name = "beql_eq", .op = .Beql, .first = X, .branch = true },
    .{ .name = "beqr_ne", .op = .Beqr, .r = .{ .op = .Add, .imm = 1 }, .first = X +% 1, .branch = false },
    .{ .name = "blel_gt", .op = .Blel, .r = .{ .op = .Shrl, .imm = 1 }, .first = X, .branch = true },
    .{ .name = "bler_eq", .op = .Bler, .first = X, .branch = false },
    .{ .name = "beqz_z", .op = .Beqz, .l = .{ .op = .And, .imm = 0 }, .r = .{ .op = .Rev }, .first = X_REV, .branch = true },
    .{ .name = "beqz_nz", .op = .Beqz, .r = .{ .op = .Rev }, .first = X_REV, .branch = false },
};

fn dyadic(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const n = dy_cases.len;

    var n_checks: usize = 0;
    for (dy_cases) |c| n_checks += if (c.second != null) 2 else 1;
    const j: Joiner = .{ .base = "dy", .n = n_checks, .out = .r("final_send"), .op = .Xor };

    var dests: [2 * n]Ref = undefined;
    for (dy_cases, 0..) |c, i| {
        dests[2 * i] = .l(b.lbl("{s}_mkl", .{c.name}));
        dests[2 * i + 1] = .l(b.lbl("{s}_mkr", .{c.name}));
    }
    const entry = b.fanout("x", &dests);

    var vals: std.ArrayList(Word) = .empty;
    var k: usize = 0;
    for (dy_cases) |c| {
        b.add(b.lbl("{s}_mkl", .{c.name}), .{ .monadic = .{ .op = c.l.op, .imm = .{ .literal = c.l.imm }, .d = .l(c.name) } });
        b.add(b.lbl("{s}_mkr", .{c.name}), .{ .monadic = .{ .op = c.r.op, .imm = .{ .literal = c.r.imm }, .d = .r(c.name) } });

        const w = b.lbl("w_{s}", .{c.name});
        if (c.branch) |right| {
            const out = c.first +% @as(Word, if (right) 0x2000 else 0x1000);
            b.add(c.name, .{ .dyadic = .{
                .slot = b.frame(),
                .matching = .Once,
                .form = .{ .arith = .{ .op = c.op, .second = .{ .label = b.lbl("{s}_pr", .{c.name}) } } },
                .d = .l(b.lbl("{s}_pl", .{c.name})),
            } });
            b.add(b.lbl("{s}_pr", .{c.name}), .{ .monadic = .{ .op = .Add, .imm = .{ .literal = 0x2000 }, .d = .l(w) } });
            b.add(b.lbl("{s}_pl", .{c.name}), .{ .monadic = .{ .op = .Add, .imm = .{ .literal = 0x1000 }, .d = .l(w) } });
            _ = b.probe(c.name, out, j.in(&b, k));
            vals.append(arena, out) catch @panic("OOM");
            k += 1;
        } else if (c.second) |sec| {
            const hi = b.lbl("{s}_hi", .{c.name});
            b.add(c.name, .{ .dyadic = .{
                .slot = b.frame(),
                .matching = .Once,
                .form = .{ .arith = .{ .op = c.op, .second = .{ .label = b.lbl("w_{s}", .{hi}) } } },
                .d = .l(w),
            } });
            _ = b.probe(hi, sec, j.in(&b, k + 1));
            _ = b.probe(c.name, c.first, j.in(&b, k));
            vals.append(arena, c.first) catch @panic("OOM");
            vals.append(arena, sec) catch @panic("OOM");
            k += 2;
        } else {
            b.add(c.name, .{ .dyadic = .{
                .slot = b.frame(),
                .matching = .Once,
                .form = .{ .arith = .{ .op = c.op } },
                .d = .l(w),
            } });
            _ = b.probe(c.name, c.first, j.in(&b, k));
            vals.append(arena, c.first) catch @panic("OOM");
            k += 1;
        }
    }
    std.debug.assert(k == n_checks);
    j.emit(&b);
    b.harness();
    return b.finish("alu_dyadic", entry, X, j.fold(vals.items), true, 1 << 16);
}

// ---------------------------------------------------------------------------
// matching: addressing modes (frame / code / absolute) and matching rules
// (Once with preloaded Present, Read, Const with preloaded and updated
// constants), including slot reuse after a match clears it.
// ---------------------------------------------------------------------------

fn matching(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const x: Word = 1000;
    const big: Word = 0x1_0000_0000;

    // Constants first so their absolute addresses are known.
    b.add("k_big", .{ .value = .{ .val = big } });
    b.add("k_three", .{ .value = .{ .val = 3 } });
    b.add("k_present_l", .{ .value = .{ .val = 50, .pb = .Present } });
    b.add("k_present_r", .{ .value = .{ .val = 50, .pb = .Present } });
    b.add("k_const", .{ .value = .{ .val = 7, .pb = .Constant } });
    b.add("k_upd", .{ .value = .{ .val = 7, .pb = .Constant } });
    b.add("k_reuse", .{ .value = .{ .val = 50, .pb = .Present } });
    const three_addr = b.addrOf("k_three");

    // a frame word written by an absolute Write, then read frame-relatively
    const fw_slot = b.frame();
    const fw_addr = root_frame + @as(sq.SqPtr, fw_slot.frame_words) * @sizeOf(Word);

    const j: Joiner = .{ .base = "m", .n = 11, .out = .r("final_send"), .op = .Add };
    var vals: [11]Word = undefined;

    const entry = b.fanout("x", &.{
        .l("once_present_l"),
        .r("once_present_r"),
        .l("read_code"),
        .r("read_abs"),
        .l("c_use0"),
        .l("c_use1"),
        .l("c_use2"),
        .l("upd_mk"),
        .l("fw_write"),
        .l("reuse_first"),
        .l("peek_const"),
    });

    // Once against a preloaded Present word: fires on first arrival.
    vals[0] = x -% 50;
    b.add("once_present_l", .{ .dyadic = .{ .slot = .{ .code = "k_present_l" }, .matching = .Once, .form = .{ .arith = .{ .op = .Sub } }, .d = .l("w_once_present_l") } });
    _ = b.probe("once_present_l", vals[0], j.in(&b, 0));
    vals[1] = 50 -% x;
    b.add("once_present_r", .{ .dyadic = .{ .slot = .{ .code = "k_present_r" }, .matching = .Once, .form = .{ .arith = .{ .op = .Sub } }, .d = .l("w_once_present_r") } });
    _ = b.probe("once_present_r", vals[1], j.in(&b, 1));

    // Read: code-relative and absolute.
    vals[2] = x +% big;
    b.add("read_code", .{ .dyadic = .{ .slot = .{ .code = "k_big" }, .matching = .Read, .form = .{ .arith = .{ .op = .Add } }, .d = .l("w_read_code") } });
    _ = b.probe("read_code", vals[2], j.in(&b, 2));
    vals[3] = 3 -% x;
    b.add("read_abs", .{ .dyadic = .{ .slot = .{ .absolute_addr = three_addr }, .matching = .Read, .form = .{ .arith = .{ .op = .Sub } }, .d = .l("w_read_abs") } });
    _ = b.probe("read_abs", vals[3], j.in(&b, 3));

    // Const against a preloaded constant: three independent left tokens.
    for (0..3) |i| {
        const name = b.lbl("c_use{d}", .{i});
        const mk = b.lbl("c_use{d}_add", .{i});
        // x + i, then * 7 from the constant slot
        b.add(name, .{ .monadic = .{ .op = .Add, .imm = .{ .literal = @intCast(i) }, .d = .l(mk) } });
        b.add(mk, .{ .dyadic = .{ .slot = .{ .code = "k_const" }, .matching = .Const, .form = .{ .arith = .{ .op = .Mul } }, .d = .l(b.lbl("w_{s}", .{name})) } });
        vals[4 + i] = (x + i) * 7;
        _ = b.probe(name, vals[4 + i], j.in(&b, 4 + i));
    }

    // Const update: a right token overwrites a Constant word and fires with
    // the old constant (7 + 100 = 107); that result comes back as a left
    // token and fires against the new constant (107 + 100 = 207).
    b.add("upd_mk", .{ .monadic = .{ .op = .Divu, .imm = .{ .literal = 10 }, .d = .r("upd") } });
    b.add("upd", .{ .dyadic = .{ .slot = .{ .code = "k_upd" }, .matching = .Const, .form = .{ .arith = .{ .op = .Add } }, .d = .l("upd_br") } });
    b.add("upd_br", .{ .monadic = .{ .op = .Blel, .imm = .{ .literal = 150 }, .d = .l("w_upd_first"), .second = .{ .label = "w_upd_second" } } });
    vals[7] = 207;
    _ = b.probe("upd_second", 207, j.in(&b, 7)); // ip + 1 of upd_br
    _ = b.probe("upd_first", 107, .l("upd"));
    b.checks.append(arena, .{ .label = "k_upd", .expected = 100 }) catch @panic("OOM");

    // Absolute Write into the frame, then a frame-relative Read of it.
    vals[8] = x *% 2;
    b.add("fw_write", .{ .write = .{ .target = .{ .addr = fw_addr }, .ack = .l("fw_read") } });
    b.add("fw_read", .{ .dyadic = .{ .slot = fw_slot, .matching = .Read, .form = .{ .arith = .{ .op = .Add } }, .d = .l("w_fw_read") } });
    _ = b.probe("fw_read", vals[8], j.in(&b, 8));

    // Slot reuse: the first token matches a preloaded Present word (950);
    // that clears it, and a fresh pair (950, 951) then meets in the same
    // slot like a normal Once join (950 - 951).
    b.add("reuse_first", .{ .dyadic = .{ .slot = .{ .code = "k_reuse" }, .matching = .Once, .form = .{ .arith = .{ .op = .Sub } }, .d = .l("reuse_br") } });
    b.add("reuse_br", .{ .monadic = .{ .op = .Blel, .imm = .{ .literal = 1000 }, .d = .l("w_reuse_a"), .second = .{ .label = "w_reuse_b" } } });
    vals[9] = 0 -% @as(Word, 1);
    _ = b.probe("reuse_b", vals[9], j.in(&b, 9)); // ip + 1 of reuse_br
    _ = b.probe("reuse_a", 950, .l("reuse_split"));
    b.add("reuse_split", .{ .monadic = .{ .op = .Dupl, .d = .l("reuse_first"), .second = .{ .label = "reuse_inc" } } });
    b.add("reuse_inc", .{ .monadic = .{ .op = .Add, .imm = .{ .literal = 1 }, .d = .r("reuse_first") } });

    // Read of a Constant word does not consume it.
    vals[10] = 7;
    b.add("peek_const", .{ .dyadic = .{ .slot = .{ .code = "k_const" }, .matching = .Read, .form = .{ .arith = .{ .op = .Dupr } }, .d = .l("w_peek_const") } });
    _ = b.probe("peek_const", 7, j.in(&b, 10));

    j.emit(&b);
    b.harness();
    return b.finish("matching", entry, x, j.fold(&vals), true, 1 << 16);
}

// ---------------------------------------------------------------------------
// write_be: byte enables, ack, writes to absolute addresses, and two
// ordered writes merging into one word.
// ---------------------------------------------------------------------------

fn mergeBytes(old: Word, new: Word, be: u8) Word {
    var mask: Word = 0;
    for (0..8) |i| {
        if ((be >> @intCast(i)) & 1 == 1) mask |= @as(Word, 0xFF) << @intCast(i * 8);
    }
    return (old & ~mask) | (new & mask);
}

fn writeBe(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const x: Word = 0x8877_6655_4433_2211;
    const init_val: Word = 0xAAAA_AAAA_AAAA_AAAA;
    const bes = [_]u8{ 0xFF, 0x01, 0x80, 0xF0, 0x0F, 0x5A, 0xA5, 0x00 };

    const n = bes.len + 2;
    const j: Joiner = .{ .base = "wb", .n = n, .out = .r("final_send"), .op = .Add };
    var vals: [n]Word = undefined;

    var dests: [bes.len + 2]Ref = undefined;
    for (0..bes.len) |i| dests[i] = .l(b.lbl("be{d}", .{i}));
    dests[bes.len] = .l("merge_lo");
    dests[bes.len + 1] = .l("abs_write");
    const entry = b.fanout("x", &dests);

    for (bes, 0..) |be, i| {
        const tgt = b.lbl("be{d}_word", .{i});
        b.add(b.lbl("be{d}", .{i}), .{ .write = .{ .target = .{ .label = tgt }, .byte_enables = be, .ack = j.in(&b, i) } });
        b.add(tgt, .{ .value = .{ .val = init_val } });
        b.checks.append(arena, .{ .label = tgt, .expected = mergeBytes(init_val, x, be) }) catch @panic("OOM");
        vals[i] = x; // the ack carries the written value through
    }

    // Two writes to one word, ordered by the first one's ack: low half from
    // x, high half from ~x.
    b.add("merge_lo", .{ .write = .{ .target = .{ .label = "merge_word" }, .byte_enables = 0x0F, .ack = .l("merge_not") } });
    b.add("merge_not", .{ .monadic = .{ .op = .Not, .d = .l("merge_hi") } });
    b.add("merge_hi", .{ .write = .{ .target = .{ .label = "merge_word" }, .byte_enables = 0xF0, .ack = j.in(&b, bes.len) } });
    b.add("merge_word", .{ .value = .{ .val = init_val } });
    b.checks.append(arena, .{ .label = "merge_word", .expected = (x & 0xFFFF_FFFF) | (~x & 0xFFFF_FFFF_0000_0000) }) catch @panic("OOM");
    vals[bes.len] = ~x;

    // Write to a raw address in the frame region, then read it back with
    // absolute addressing.
    const scratch: sq.SqPtr = root_frame + 0x100 + 8; // word 1 of the frame's second pb group
    b.add("abs_write", .{ .write = .{ .target = .{ .addr = scratch }, .ack = .l("abs_read") } });
    b.add("abs_read", .{ .dyadic = .{ .slot = .{ .absolute_addr = scratch }, .matching = .Read, .form = .{ .arith = .{ .op = .Xor } }, .d = .l("w_abs_read") } });
    _ = b.probe("abs_read", 0, j.in(&b, bes.len + 1));
    vals[bes.len + 1] = 0;

    j.emit(&b);
    b.harness();
    return b.finish("write_be", entry, x, j.fold(&vals), true, 1 << 16);
}

// ---------------------------------------------------------------------------
// call: Extract minting tags, Send delivering to a minted tag (with Send's
// own destination also firing), and a call into a child frame that returns
// through a passed return-address tag.
// ---------------------------------------------------------------------------

const child_offset_words: Word = 64; // two pb groups past the root frame

fn call(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const x: Word = 21;

    b.add("k_child", .{ .value = .{ .val = child_offset_words << fp_shift } });

    // the callee's result reaches the join through after_call
    const j: Joiner = .{ .base = "c", .n = 3, .out = .r("final_send"), .op = .Add };
    var vals: [3]Word = undefined;

    const entry = b.fanout("x", &.{
        // local send
        .l("ext_tgt"),
        .l("val_mk"),
        .l("tgt"),
        // call
        .l("ext_arg"),
        .l("ext_ra_slot"),
        .l("ext_ret"),
        .r("send_arg"),
        .l("after_call"),
    });

    // Local send: mint a tag for tgt.R in this frame, send x + 100 to it.
    // Send also passes the value on to its own d.
    b.add("ext_tgt", .{ .extract = .{ .mint = .r("tgt"), .d = .l("send_local") } });
    b.add("val_mk", .{ .monadic = .{ .op = .Add, .imm = .{ .literal = 100 }, .d = .r("send_local") } });
    b.add("send_local", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .send, .d = .l("w_send_d") } });
    vals[0] = x + 100;
    _ = b.probe("send_d", vals[0], j.in(&b, 0));
    b.add("tgt", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .{ .arith = .{ .op = .Sub } }, .d = .l("w_tgt") } });
    vals[1] = x -% (x + 100);
    _ = b.probe("tgt", vals[1], j.in(&b, 1));

    // Call: callee(x) = 3x + 1 runs in a child frame at fp + 64 words.
    b.add("ext_arg", .{ .extract = .{ .mint = .l("callee"), .d = .l("child_arg") } });
    b.add("child_arg", .{ .dyadic = .{ .slot = .{ .code = "k_child" }, .matching = .Read, .form = .{ .arith = .{ .op = .Add } }, .d = .l("send_arg") } });
    b.add("send_arg", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .send, .d = .halt } });

    b.add("ext_ra_slot", .{ .extract = .{ .mint = .l("csend"), .d = .l("child_ra") } });
    b.add("child_ra", .{ .dyadic = .{ .slot = .{ .code = "k_child" }, .matching = .Read, .form = .{ .arith = .{ .op = .Add } }, .d = .l("send_ra") } });
    b.add("ext_ret", .{ .extract = .{ .mint = .r("after_call"), .d = .r("send_ra") } });
    b.add("send_ra", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .send, .d = .halt } });

    // callee, running with fp = root + 64 words
    b.add("callee", .{ .monadic = .{ .op = .Mul, .imm = .{ .literal = 3 }, .d = .l("callee_inc") } });
    b.add("callee_inc", .{ .monadic = .{ .op = .Add, .imm = .{ .literal = 1 }, .d = .l("w_callee") } });
    _ = b.probe("callee", 3 * x + 1, .r("csend"));
    b.add("csend", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .send, .d = .halt } });

    // back in the caller frame
    b.add("after_call", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .{ .arith = .{ .op = .Add } }, .d = .l("w_after_call") } });
    vals[2] = x + (3 * x + 1);
    _ = b.probe("after_call", vals[2], j.in(&b, 2));

    j.emit(&b);
    b.harness();
    return b.finish("call", entry, x, j.fold(&vals), true, 1 << 16);
}

// ---------------------------------------------------------------------------
// sum_loop: a loop that reuses its matching slots every iteration.
// result = n + (n-1) + ... + 1. The decremented counter is held at `sync`
// until the new sum exists, so no slot ever sees tokens from two iterations.
// ---------------------------------------------------------------------------

fn sumLoop(arena: std.mem.Allocator) P.Program {
    var b: Builder = .init(arena);
    const n: Word = 10;

    b.add("entry", .{ .monadic = .{ .op = .Dupl, .d = .l("loop_i"), .second = .{ .label = "zero" } } });
    b.add("zero", .{ .monadic = .{ .op = .And, .imm = .{ .literal = 0 }, .d = .r("gate") } });

    b.add("loop_i", .{ .monadic = .{ .op = .Dupl, .d = .l("gate"), .second = .{ .label = "test" } } });
    // i == 0 → drop; else continue
    b.add("test", .{ .monadic = .{ .op = .Blel, .imm = .{ .literal = 0 }, .d = .halt, .second = .{ .label = "nz" } } });
    b.add("nz", .{ .monadic = .{ .op = .Dupl, .d = .l("add"), .second = .{ .label = "dec" } } });
    b.add("dec", .{ .monadic = .{ .op = .Add, .imm = .{ .literal = -1 }, .d = .l("sync") } });
    // [L = i, R = acc]: i != 0 → acc to add; i == 0 → acc to exit
    b.add("gate", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .{ .arith = .{ .op = .Beqz, .second = .{ .label = "exit" } } }, .d = .r("add") } });
    b.add("exit", .{ .monadic = .{ .d = .l("w_sum") } });
    b.add("add", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .{ .arith = .{ .op = .Add } }, .d = .l("acc_fan") } });
    b.add("acc_fan", .{ .monadic = .{ .op = .Dupl, .d = .r("sync"), .second = .{ .label = "acc_fwd" } } });
    b.add("acc_fwd", .{ .monadic = .{ .d = .r("gate") } });
    // [L = i - 1, R = new acc] → i - 1
    b.add("sync", .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .{ .arith = .{ .op = .Dupl } }, .d = .l("loop_i") } });

    _ = b.probe("sum", n * (n + 1) / 2, .r("final_send"));
    b.harness();
    return b.finish("sum_loop", "entry", n, n * (n + 1) / 2, false, 1 << 20);
}

// ---------------------------------------------------------------------------
// rand_*: seeded random straight-line programs. Every step's output (and
// second output, if any) is a check word, so the first diverging check is
// the first wrong instruction. Expectations come from the model itself.
// ---------------------------------------------------------------------------

const arith_ops = [_]sq.AluOp{ .Nop, .Add, .Sub, .Mul, .Div, .Divu, .Rem, .Mod, .And, .Or, .Xor, .Shl, .Shrl, .Shra, .Not, .Rev, .Dupl, .Dupr };
const branch_ops = [_]sq.AluOp{ .Beqz, .Beql, .Beqr, .Bler, .Blel };

fn hasSecond(op: sq.AluOp) bool {
    return switch (op) {
        .And, .Or, .Xor, .Shl, .Shrl, .Shra => false,
        else => true,
    };
}

fn randImm(r: std.Random) i32 {
    return switch (r.uintLessThan(u8, 6)) {
        0 => r.intRangeAtMost(i32, -8, 8),
        1 => ([_]i32{ 0, 1, -1, std.math.minInt(i32), std.math.maxInt(i32), 63, 64 })[r.uintLessThan(usize, 7)],
        else => r.int(i32),
    };
}

/// i64 min divided by -1 traps in the model, so never divide a token by an
/// immediate -1.
fn safeImm(r: std.Random, op: sq.AluOp, port: sq.Port) i32 {
    while (true) {
        const imm = randImm(r);
        const divides_token = port == .Left and (op == .Div or op == .Rem or op == .Mod);
        if (divides_token and imm == -1) continue;
        return imm;
    }
}

fn randomChain(arena: std.mem.Allocator, seed: u64, steps: usize) P.Program {
    var b: Builder = .init(arena);
    var prng: std.Random.DefaultPrng = .init(seed);
    const r = prng.random();

    for (0..steps) |i| {
        const here = b.lbl("s{d}", .{i});
        const next: Ref = if (i + 1 == steps) .r("final_send") else .l(b.lbl("s{d}", .{i + 1}));
        const w = b.lbl("w_s{d}", .{i});
        const port: sq.Port = if (r.boolean()) .Left else .Right;

        switch (r.uintLessThan(u8, 10)) {
            // monadic op, maybe with a second output joined back in
            0...4 => {
                const op = arith_ops[r.uintLessThan(usize, arith_ops.len)];
                const with_second = hasSecond(op) and r.boolean();
                // entry point is a Nop that steers the token onto `port`
                b.add(here, .{ .monadic = .{ .d = .{ .node = .{ .label = b.lbl("s{d}_op", .{i}), .port = port } } } });
                const sync = b.lbl("s{d}_sync", .{i});
                b.add(b.lbl("s{d}_op", .{i}), .{ .monadic = .{
                    .op = op,
                    .imm = .{ .literal = safeImm(r, op, port) },
                    .d = .l(w),
                    .second = if (with_second) .{ .label = b.lbl("w_s{d}_hi", .{i}) } else null,
                } });
                if (with_second) {
                    _ = b.probe(b.lbl("s{d}_hi", .{i}), null, .r(sync));
                    _ = b.probe(b.lbl("s{d}", .{i}), null, .l(sync));
                    // forward the main value once both are written
                    b.add(sync, .{ .dyadic = .{ .slot = b.frame(), .matching = .Once, .form = .{ .arith = .{ .op = .Dupl } }, .d = next } });
                } else {
                    _ = b.probe(b.lbl("s{d}", .{i}), null, next);
                }
            },
            // switch op: marked paths into one check
            5...6 => {
                const op = branch_ops[r.uintLessThan(usize, branch_ops.len)];
                b.add(here, .{ .monadic = .{ .d = .{ .node = .{ .label = b.lbl("s{d}_op", .{i}), .port = port } } } });
                b.add(b.lbl("s{d}_op", .{i}), .{ .monadic = .{
                    .op = op,
                    .imm = .{ .literal = randImm(r) },
                    .d = .l(b.lbl("s{d}_pl", .{i})),
                    .second = .{ .label = b.lbl("s{d}_pr", .{i}) },
                } });
                b.add(b.lbl("s{d}_pr", .{i}), .{ .monadic = .{ .op = .Xor, .imm = .{ .literal = r.int(i32) }, .d = .l(w) } });
                b.add(b.lbl("s{d}_pl", .{i}), .{ .monadic = .{ .op = .Add, .imm = .{ .literal = r.int(i32) }, .d = .l(w) } });
                _ = b.probe(b.lbl("s{d}", .{i}), null, next);
            },
            // dyadic op against a random 64-bit constant, code or absolute
            else => {
                const op = arith_ops[r.uintLessThan(usize, arith_ops.len)];
                var k = r.int(Word);
                if (op == .Div or op == .Rem or op == .Mod) {
                    if (k == ~@as(Word, 0)) k = 3;
                }
                const kl = b.lbl("s{d}_k", .{i});
                b.add(kl, .{ .value = .{ .val = k } });
                const slot: a.Slot = if (r.boolean()) .{ .code = kl } else .{ .absolute_addr = b.addrOf(kl) };
                b.add(here, .{ .dyadic = .{
                    .slot = slot,
                    .matching = .Read,
                    // token arrives on the left; Read puts the constant on the right
                    .form = .{ .arith = .{ .op = op } },
                    .d = .l(w),
                } });
                _ = b.probe(b.lbl("s{d}", .{i}), null, next);
            },
        }
    }
    b.harness();
    const name = b.lbl("rand_{x:0>4}", .{seed});
    return b.finish(name, "s0", r.int(Word), null, true, 1 << 16);
}

pub const random_seeds = [_]u64{ 0x0001, 0x0002, 0x0003, 0x0004, 0x0005, 0x0006, 0x0007, 0x0008 };
const random_steps = 48;

/// Every test program, built into `arena`.
pub fn all(arena: std.mem.Allocator) ![]const P.Program {
    var list: std.ArrayList(P.Program) = .empty;
    try list.append(arena, aluImm(arena));
    try list.append(arena, aluSecond(arena));
    try list.append(arena, branchImm(arena));
    try list.append(arena, dyadic(arena));
    try list.append(arena, matching(arena));
    try list.append(arena, writeBe(arena));
    try list.append(arena, call(arena));
    try list.append(arena, sumLoop(arena));
    for (random_seeds) |seed| try list.append(arena, randomChain(arena, seed, random_steps));
    return list.items;
}
