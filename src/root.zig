const std = @import("std");
const Io = std.Io;

pub const SqPtr = u32;
pub const Port = enum(u1) { Left, Right };

pub fn AlignedSqPtr(a: comptime_int) type {
    return packed struct {
        repr: @Int(.unsigned, @typeInfo(SqPtr).int.bits - a),

        pub const Error = error{Misaligned};

        pub fn parse(ptr: SqPtr) Error!AlignedSqPtr(a) {
            if (ptr & ((2 << a) - 1) != 0) return Error.Misaligned;
            return .{ .repr = @intCast(ptr >> a) };
        }

        pub fn addr(self: AlignedSqPtr(a)) SqPtr {
            return @as(SqPtr, self.repr) << a;
        }
    };
}

/// Small enough to fit in the non-pb part of a word
pub const Tag = packed struct(u62) {
    // 4 byte == word aligned
    ip: AlignedSqPtr(4),
    fp: AlignedSqPtr(3),
    port: Port,
    pad: u4 = 0,

    pub fn init(ip: AlignedSqPtr(4), fp: AlignedSqPtr(3), port: Port) Tag {
        return .{ .ip = ip, .fp = fp, .port = port };
    }

    pub fn offsetWith(self: Tag, dest: Dest) Tag {
        return .{
            .ip = .parse(@intCast((@as(PtrArith, dest.offset) << 3) +% @as(PtrArith, self.ip.addr()))),
            .fp = self.fp,
            .port = dest.port,
        };
    }
};
pub const Word = u64; // accumulator / memory word
pub const EffWord = u62; // alu / non-pb word
/// Wide enough to hold any SqPtr plus a signed instruction offset without wrapping.
pub const PtrArith = i34;
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
    addr: u11, // interpreted as signed for code relative constants
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
    forming_rule_payload: packed union(u6) {
        arith: packed struct(u6) { alu_op: AluOp },
        nothing: u6,
    },
    pad: u19,
};
pub const Instr = packed struct(u64) {
    tag: enum(u2) { Monadic, Dyadic, Write },
    data: packed union {
        monadic: MonadicInstr,
        dyadic: DyadicInstr,
        write: packed struct(u62) {
            ptr: SqPtr,
            pad: u30,
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
                if (token.tag.port == .Left) token.acc else data.imm,
                if (token.tag.port == .Right) token.acc else data.imm,
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
            // claude plz
        },
        .Write => {
            state.write(Word, instr.data.write.ptr, token.acc);
        }
    }
}

//     if (instr.token_matching_rule == .Monadic) {
//         // dont resolve the other token
//         const maybe_res_l, const maybe_res_r =
//             apply_alu(instr.alu_op, token.acc, instr.payload.imm);
//         const maybe_token_l, const maybe_token_r = form_tokens(
//             token,
//             instr,
//             maybe_res_l,
//             maybe_res_r,
//         );

//         if (maybe_token_l) |t| state.push(t);
//         if (maybe_token_r) |t| state.push(t);
//         return;
//     }

//     const effective_address: SqPtr = switch (instr.addr_tag) {
//         .FrameRelative => @intCast(@as(PtrArith, token.tag.fp.addr()) + @as(PtrArith, instr.addr.unsigned)),
//         .CodeRelative => @intCast(@as(PtrArith, token.tag.ip) + instr.addr.signed),
//         .Absolute => instr.addr.unsigned,
//     };

//     const other: MemValue = @bitCast(state.read(MemValue, effective_address));
//     if (other.pb == .Empty) { // the value is garbage
//         const new_pb: PresenceBits =
//             if (instr.token_matching_rule == .ConstDyadic and token.tag.port == .Right)
//                 .Constant
//             else
//                 .Present;
//         state.write(
//             MemValue,
//             effective_address,
//             .{ .pb = new_pb, .val = @truncate(token.acc) },
//         );
//         return; // and wait for our other token to join :D
//     } else if (other.pb == .Present) {
//         const new_pb: PresenceBits =
//             if (instr.token_matching_rule == .ConstDyadic and token.tag.port == .Right)
//                 .Constant
//             else
//                 .Empty;
//         state.write(
//             MemValue,
//             effective_address,
//             .{ .pb = new_pb, .val = @truncate(token.acc) },
//         );
//     }

//     const other_acc: Word = other.val; // gangalang what are our signedness semantics
//     const maybe_res_l, const maybe_res_r = apply_alu(
//         instr.alu_op,
//         if (token.tag.port == .Left) token.acc else other_acc,
//         if (token.tag.port == .Right) token.acc else other_acc,
//     );
//     const maybe_token_l, const maybe_token_r = form_tokens(
//         token,
//         instr,
//         maybe_res_l,
//         maybe_res_r,
//     );

//     if (maybe_token_l) |t| state.push(t);
//     if (maybe_token_r) |t| state.push(t);
// }

fn apply_alu(op: AluOp, val_l: Word, val_r: Word) struct { ?Word, ?Word } {
    return switch (op) {
        .nop => .{ val_l, val_r },
        .add => {
            const res, const ov = @addWithOverflow(val_l, val_r);
            return .{ res, ov };
        },
        else => unreachable, // todo
    };
}

fn form_tokens(from: Token, instr: Instr, val_l: ?Word, val_r: ?Word) struct { ?Token, ?Token } {
    var res: struct { ?Token, ?Token } = .{ null, null };
    switch (instr.token_forming_rule) {
        .Arith => {
            if (val_l) |v| {
                res.@"0" = Token{ .tag = from.tag.offsetWith(instr.d1), .acc = v };
            }
            if (val_r) |v| {
                res.@"1" = Token{ .tag = from.tag.offsetWith(instr.d2), .acc = v };
            }
            return res;
        },
        .Switch => {
            if (val_r) |condition| {
                if (val_l) |v| {
                    const taken = Token{ .tag = from.tag.offsetWith(instr.d2), .acc = v };
                    if (condition != 0) res.@"0" = taken else res.@"1" = taken;
                }
            }
            // empty when one of these is missing; should never happen
            return res;
        },
        .Send => {
            if (val_l) |tag| {
                if (val_r) |v| {
                    res.@"0" = .{
                        .tag = @bitCast(@as(
                            @typeInfo(Tag).@"struct".backing_integer orelse unreachable(),
                            @truncate(tag),
                        )),
                        .acc = v,
                    };
                    res.@"1" = Token{ .tag = from.tag.offsetWith(instr.d1), .acc = v };
                }
            }
            // as before, we should always have both values for this
            return res;
        },
        .Extract => {
            res.@"0" = Token{
                .tag = from.tag.offsetWith(instr.d1),
                .acc = @as(EffWord, @bitCast(from.tag.offsetWith(instr.d2))),
            };
            return res;
        },
    }
}
