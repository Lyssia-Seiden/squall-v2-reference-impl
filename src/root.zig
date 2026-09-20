const std = @import("std");
const Io = std.Io;

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
        std.testing.expectEqual(i % 4 == 0, AlignedSqPtr(2).parse(i) != .Misaligned);
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
pub const EffWord = u62; // alu / non-pb word

pub fn extendImm(imm: i32) Word {
    return @bitCast(@as(@Int(.signed, @typeInfo(Word).int.bits), imm));
}

pub const Token = packed struct(u128) {
    pad: u2 = 0,
    tag: Tag,
    acc: Word,
};

pub const PresenceBits = enum(u2) { Empty, Present, Constant };
pub const MemValue = packed struct(u64) { pb: PresenceBits, val: u62 };

/// offset is in instructions, not bytes
pub const Dest = packed struct { offset: i20, port: Port };
pub const AluOp = enum(u6) {
    // binary
    Nop,
    Add,
    Sub,
    And,
    Or,
    Xor,
    Mul,
    Div,
    Shl,
    Shrl,
    Shra,
    // unary
    Not,
    Rev,
    // switch - two operands, one of two outputs
    Beqz,
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
        arith: packed struct(u24) { alu_op: AluOp, pad: u18 = 0 },
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
                if (token.tag.port == .Left) token.acc else extendImm(data.imm),
                if (token.tag.port == .Right) token.acc else extendImm(data.imm),
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

            const other_acc: Word = other.val;
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
                    // todo how handle r token when generated
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
                                .tag = token.tag.offsetWith(data.dyadic.d),
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
        .Shl => .{ val_l << @truncate(val_r), null },
        else => unreachable, // todo
    };
}
