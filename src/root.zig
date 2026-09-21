const std = @import("std");
const Io = std.Io;

pub const assembler = @import("assembler.zig");

test {
    _ = assembler;
}

pub const SqPtr = u32;
pub const Port = enum(u1) { Left, Right };

pub fn AlignedSqPtr(a: comptime_int) type {
    return packed struct {
        repr: Repr,

        const Self = @This();
        pub const Repr = @Int(.unsigned, @typeInfo(SqPtr).int.bits - a);
        pub const SignedRepr = @Int(.signed, @typeInfo(SqPtr).int.bits - a);

        pub const Error = error{Misaligned};

        pub fn parse(ptr: SqPtr) Error!Self {
            if (ptr & ((1 << a) - 1) != 0) return Error.Misaligned;
            return .{ .repr = @intCast(ptr >> a) };
        }

        pub fn addr(self: Self) SqPtr {
            return @as(SqPtr, self.repr) << a;
        }

        pub fn offsetBy(self: Self, units: anytype) Self {
            const delta: Repr = if (@typeInfo(@TypeOf(units)).int.signedness == .signed)
                @bitCast(@as(SignedRepr, units))
            else
                units;
            return .{ .repr = self.repr +% delta };
        }
    };
}

test "sqptr align" {
    for (0..64) |i| {
        const aligned = if (AlignedSqPtr(2).parse(@intCast(i))) |_| true else |_| false;
        try std.testing.expectEqual(i % 4 == 0, aligned);
    }
}

/// Small enough to fit in the non-pb part of a word
pub const Tag = packed struct(u62) {
    // 2^3 == 8 byte == word aligned
    ip: AlignedSqPtr(3),
    fp: AlignedSqPtr(3),
    port: Port,
    pad: u3 = 0,

    pub fn init(ip: AlignedSqPtr(3), fp: AlignedSqPtr(3), port: Port) Tag {
        return .{ .ip = ip, .fp = fp, .port = port };
    }

    pub fn offsetWith(self: Tag, dest: Dest) Tag {
        return .{
            .ip = self.ip.offsetBy(dest.offset),
            .fp = self.fp,
            .port = dest.port,
        };
    }
};
pub const Word = u64; // accumulator / memory word
pub const SignedWord = i64; // accumulator / memory word
pub const EffWord = u62; // alu / non-pb word

pub fn signExtend(val: anytype) Word {
    const ty = @typeInfo(@TypeOf(val));
    const signed = @as(@Int(.signed, ty.int.bits), if (ty.int.signedness == .unsigned) @bitCast(val) else val);
    return @bitCast(@as(@Int(.signed, @typeInfo(Word).int.bits), signed));
}

pub const Token = packed struct(u128) {
    pad: u2 = 0,
    tag: Tag,
    acc: Word,
};

pub const PresenceBits = enum(u2) { Empty, Present, Constant };
pub const MemValue = packed struct(u64) { val: u62, pb: PresenceBits };

/// offset is in instructions, not bytes
pub const Dest = packed struct { offset: i20, port: Port };
pub const AluOp = enum(u6) {
    // binary
    Nop = 0,
    Add = 4,
    Sub,
    Mul,
    Div,
    Rem,
    Mod,
    And = 16,
    Or,
    Xor,
    Shl,
    Shrl,
    Shra,
    // unary
    Not = 24,
    Rev,
    Dupl,
    Dupr,
    // switch - two operands, one of two outputs
    Beqz = 32,
    Beql,
    Beqr,
};
pub const MonadicInstr = packed struct(u62) {
    alu_op: AluOp,
    pad: u1 = 0,
    d: Dest,
    send_second_token: bool, // on true we send to { second_token_port, +8 bytes }
    second_token_port: Port, // only meaningful if above is set
    imm: i32,
};
pub const DyadicInstr = packed struct(u62) {
    // interpreted as signed for code relative constants
    // words not bytes
    addr: u11,
    addr_tag: enum(u2) {
        FrameRelative,
        CodeRelative,
        Absolute,
    },

    // once writes Present into any Empty word, and writes Empty into any other.
    // const writes Const on the right token, Present on the left, and stays Const once written
    // read takes the full value of a location unconditionally
    matching_rule: enum(u2) { Once, Const, Read },
    d: Dest,
    forming_rule_tag: enum(u2) { Arith, Reserved, Extract, Send },
    forming_rule_payload: packed union(u24) {
        arith: packed struct(u24) {
            alu_op: AluOp,
            send_second_token: bool, // on true we send to { second_token_port, +8 bytes }
            second_token_port: Port, // only meaningful if above is set
            pad: u16 = 0,
        },
        // the tag Extract mints points here, rather than at `d`
        extract: packed struct(u24) { d2: Dest, pad: u3 = 0 },
        nothing: u24,
    },
};
pub const Instr = packed struct(u64) {
    tag: enum(u2) { Monadic, Dyadic, Write },
    data: packed union {
        monadic: MonadicInstr,
        dyadic: DyadicInstr,
        write: packed struct(u62) {
            ptr: AlignedSqPtr(3),
            pad: u33 = 0,
        },
    },
};

pub const State = struct {
    stackBase: SqPtr,
    stackTop: SqPtr,

    memory: std.AutoHashMap(SqPtr, u8),

    pub fn read(self: *const State, comptime ty: type, addr: SqPtr) [@bitSizeOf(ty) / 8]u8 {
        const width = @bitSizeOf(ty);
        var res: [width / 8]u8 = [_]u8{0} ** (width / 8);
        for (0..width / 8) |i| {
            res[i] = if (self.memory.get(@truncate(addr + i))) |v| v else 0;
        }
        return res;
    }
    pub fn write(self: *State, comptime valT: type, addr: SqPtr, val: valT) void {
        const width = @bitSizeOf(valT);
        for (0..width / 8) |i| {
            self.memory.put(@truncate(addr + i), @as([width / 8]u8, @bitCast(val))[i]) catch unreachable; // this is false, but im lazy.
        }
    }

    pub fn push(self: *State, token: Token) void {
        self.write(Token, self.stackTop, token);
        self.stackTop -= @sizeOf(Token);
    }

    pub fn pop(self: *State) ?Token {
        if (self.stackTop >= self.stackBase) return null;
        self.stackTop += @sizeOf(Token);
        return @as(Token, @bitCast(self.read(Token, self.stackTop)));
    }
};

pub fn clock(state: *State) void {
    const token = if (state.pop()) |t| t else return;
    // Absolute(0) address is a dump
    std.debug.print("{}\n", .{token});
    if (token.tag.ip.addr() == 0x00) return;
    clock_token(state, token);
}

fn clock_token(state: *State, token: Token) void {
    const instr: Instr = @bitCast(state.read(Instr, token.tag.ip.addr()));

    switch (instr.tag) {
        .Monadic => {
            const data = instr.data.monadic;
            const maybe_l, const maybe_r = apply_alu(
                data.alu_op,
                if (token.tag.port == .Left) token.acc else signExtend(data.imm),
                if (token.tag.port == .Right) token.acc else signExtend(data.imm),
            );
            if (maybe_l) |l| {
                state.push(.{ .tag = token.tag.offsetWith(data.d), .acc = l });
            }
            if (maybe_r) |r| {
                if (data.send_second_token) {
                    state.push(.{
                        .tag = token.tag.offsetWith(.{
                            .offset = 1,
                            .port = data.second_token_port,
                        }),
                        .acc = r,
                    });
                }
            }
        },
        .Dyadic => {
            const data = instr.data.dyadic;
            const slot: AlignedSqPtr(3) = switch (data.addr_tag) {
                .FrameRelative => token.tag.fp.offsetBy(data.addr),
                .CodeRelative => token.tag.ip.offsetBy(@as(i11, @bitCast(data.addr))),
                .Absolute => .{ .repr = data.addr },
            };
            const addr = slot.addr();

            const other: MemValue = @bitCast(state.read(MemValue, addr));
            if (data.matching_rule != .Read) {
                if (other.pb == .Empty) {
                    const new_pb: PresenceBits =
                        if (data.matching_rule == .Const and token.tag.port == .Right)
                            .Constant
                        else
                            .Present;
                    state.write(MemValue, addr, .{
                        .pb = new_pb,
                        .val = @truncate(token.acc),
                    });
                    return;
                } else if (other.pb == .Present) {
                    const new_pb: PresenceBits =
                        if (data.matching_rule == .Const and token.tag.port == .Right)
                            .Constant
                        else
                            .Empty;
                    state.write(MemValue, addr, .{
                        .pb = new_pb,
                        .val = @truncate(token.acc),
                    });
                }
            }

            const other_acc: Word = signExtend(other.val);
            const maybe_l, const maybe_r = apply_alu(
                switch (data.forming_rule_tag) {
                    .Arith => data.forming_rule_payload.arith.alu_op,
                    else => .Nop,
                },
                if (token.tag.port == .Left) token.acc else other_acc,
                if (token.tag.port == .Right) token.acc else other_acc,
            );

            switch (data.forming_rule_tag) {
                .Arith => {
                    if (maybe_l) |v| {
                        state.push(.{ .tag = token.tag.offsetWith(data.d), .acc = v });
                    }
                    if (maybe_r) |v| {
                        if (data.forming_rule_payload.arith.send_second_token) {
                            state.push(.{
                                .tag = token.tag.offsetWith(.{
                                    .offset = 1,
                                    .port = data.forming_rule_payload.arith.second_token_port,
                                }),
                                .acc = v,
                            });
                        }
                    }
                },
                .Send => {
                    // both should always exist
                    if (maybe_l) |tag| {
                        if (maybe_r) |v| {
                            state.push(.{
                                .tag = @bitCast(@as(
                                    @typeInfo(Tag).@"struct".backing_integer orelse unreachable,
                                    @truncate(tag),
                                )),
                                .acc = v,
                            });
                            state.push(.{
                                .tag = token.tag.offsetWith(data.d),
                                .acc = v,
                            });
                        }
                    }
                },
                .Extract => {
                    const minted = token.tag.offsetWith(data.forming_rule_payload.extract.d2);
                    state.push(.{
                        .tag = token.tag.offsetWith(data.d),
                        .acc = @as(EffWord, @bitCast(minted)),
                    });
                },
                .Reserved => unreachable,
            }
        },
        .Write => {
            state.write(Word, instr.data.write.ptr.addr(), token.acc);
        },
    }
}

fn apply_alu(op: AluOp, val_l: Word, val_r: Word) struct { ?Word, ?Word } {
    return switch (op) {
        .Nop => .{ val_l, val_r },
        .Add => {
            const res, const ov = @addWithOverflow(val_l, val_r);
            return .{ res, ov };
        },
        .Sub => {
            const res, const ov = @subWithOverflow(val_l, val_r);
            return .{ res, ov };
        },
        .Mul => {
            const res = @as(u128, val_l) * @as(u128, val_r);
            return .{ @truncate(res), @truncate(res >> 64) };
        },
        .Div => {
            var flags: packed struct { divByZero: bool, truncated: bool } = @bitCast(@as(u2, 0));
            var res: Word = 0;
            if (val_r == 0) {
                flags.divByZero = true;
            } else {
                flags.divByZero = false;
                res = @divTrunc(val_l, val_r);
                if (@rem(val_l, val_r) != 0) flags.truncated = true;
            }
            return .{ res, @as(u2, @bitCast(flags)) };
        },
        .Mod => {
            var flags: packed struct { divByZero: bool } = @bitCast(@as(u1, 0));
            var res: Word = 0;
            if (val_r == 0) {
                flags.divByZero = true;
            } else {
                flags.divByZero = false;
                res = @mod(val_l, val_r);
            }
            return .{ res, @as(u1, @bitCast(flags)) };
        },
        .Rem => {
            var flags: packed struct { divByZero: bool } = @bitCast(@as(u1, 0));
            var res: Word = 0;
            if (val_r == 0) {
                flags.divByZero = true;
            } else {
                flags.divByZero = false;
                res = @rem(val_l, val_r);
            }
            return .{ res, @as(u1, @bitCast(flags)) };
        },
        .Shl => .{ val_l << @truncate(val_r), null },
        .Shrl => .{ val_l >> @truncate(val_r), null },
        .Shra => .{ @as(Word, @bitCast(@as(SignedWord, @bitCast(val_l)) >> @truncate(val_r))), null },
        .And => .{ val_l & val_r, null },
        .Or => .{ val_l | val_r, null },
        .Xor => .{ val_l ^ val_r, null },
        .Not => .{ ~val_l, ~val_r },
        .Rev => .{ @bitReverse(val_l), @bitReverse(val_r) },
        .Dupl => .{ val_l, val_l },
        .Dupr => .{ val_r, val_r },
        .Beqz => .{
            if (val_l != 0) val_r else null,
            if (val_l == 0) val_r else null,
        },
        .Beql => .{
            if (val_l != val_r) val_l else null,
            if (val_l == val_r) val_l else null,
        },
        .Beqr => .{
            if (val_l != val_r) val_r else null,
            if (val_l == val_r) val_r else null,
        },
    };
}
