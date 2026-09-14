const std = @import("std");
const Io = std.Io;

const SqPtr = u40;
const Port = enum(u1) { Left, Right };
const Tag = packed struct(u81) {
    ip: SqPtr,
    fp: SqPtr,
    port: Port,
};
const Token = packed struct(u256) {
    tag: Tag,
    acc: u128,
    // we should use this for something!
    pad: u47 = 0,
};

const PresenceBits = enum(u2) { Empty, Present, Constant };
const MemValue = packed struct(u128) { pb: PresenceBits, val: u126 };

const Dest = packed struct { offset: i20, port: Port };
const AluOp = enum(u5) { nop, add, sub, and_, or_, xor, not, mul, div, shl, shrl, shra };
const Instr = packed struct(u64) {
    addr: packed union(u11) {
        signed: i11,
        unsigned: u11,
    },
    addr_tag: enum(u2) {
        FrameRelative,
        CodeRelative,
        Absolute,
    },
    // todo make monadic really its own thing
    token_matching_rule: enum(u2) { Dyadic, Monadic, ConstDyadic },
    alu_op: AluOp,
    token_forming_rule: enum(u2) { Arith, Switch, Extract, Send },
    d1: Dest,
    d2: Dest,
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
    clock_token(state, token);
}

fn clock_token(state: *State, token: Token) void {
    const instr: Instr = @bitCast(state.read(Instr, token.tag.ip));
    const effective_address: SqPtr = switch (instr.addr_tag) {
        .FrameRelative => @intCast(@as(i41, token.tag.fp) + @as(SqPtr, @intCast(instr.addr.unsigned))),
        .CodeRelative => @intCast(@as(i41, token.tag.ip) + instr.addr.signed),
        .Absolute => instr.addr.unsigned,
    };

    if (instr.token_matching_rule == .Monadic) {
        // dont resolve the other token
        const maybe_res_l, const maybe_res_r =
            apply_alu(instr.alu_op, token.acc, token.acc);
        const maybe_token_l, const maybe_token_r = form_tokens(
            token,
            instr,
            maybe_res_l,
            maybe_res_r,
        );

        if (maybe_token_l) |t| state.push(t);
        if (maybe_token_r) |t| state.push(t);
        return;
    }

    const other: MemValue = @bitCast(state.read(MemValue, effective_address));
    if (other.pb == .Empty) { // the value is garbage
        const new_pb: PresenceBits =
            if (instr.token_matching_rule == .ConstDyadic and token.tag.port == .Right)
                .Constant
            else
                .Present;
        state.write(
            u128,
            effective_address,
            (@as(u128, @intFromEnum(new_pb)) << 126) | @as(u126, @truncate(token.acc)),
        );
        return; // and wait for our other token to join :D
    } else if (other.pb == .Present) {
        const new_pb: PresenceBits =
            if (instr.token_matching_rule == .ConstDyadic and token.tag.port == .Right)
                .Constant
            else
                .Empty;
        state.write(
            u128,
            effective_address,
            (@as(u128, @intFromEnum(new_pb)) << 126) | @as(u126, @truncate(token.acc)),
        );
    }

    const other_acc: u126 = other.val; // gangalang what are our signedness semantics
    const maybe_res_l, const maybe_res_r = apply_alu(
        instr.alu_op,
        if (token.tag.port == .Left) token.acc else other_acc,
        if (token.tag.port == .Right) token.acc else other_acc,
    );
    const maybe_token_l, const maybe_token_r = form_tokens(
        token,
        instr,
        maybe_res_l,
        maybe_res_r,
    );

    if (maybe_token_l) |t| state.push(t);
    if (maybe_token_r) |t| state.push(t);
}

fn apply_alu(op: AluOp, val_l: u128, val_r: u128) struct { ?u128, ?u128 } {
    return switch (op) {
        .nop => .{ val_l, val_r },
        .add => {
            const res, const ov = @addWithOverflow(val_l, val_r);
            return .{ res, ov };
        },
        else => unreachable(), // todo
    };
}

fn form_tokens(from: Token, instr: Instr, val_l: ?u128, val_r: ?u128) struct { ?Token, ?Token } {
    var res: struct { ?Token, ?Token } = .{ null, null };
    switch (instr.token_forming_rule) {
        .Arith => {
            if (val_l) |v| {
                res.@"0" = Token{
                    .tag = .{
                        .ip = @intCast(instr.d1.offset + @as(i41, @intCast(from.tag.ip))),
                        .fp = from.tag.fp,
                        .port = instr.d1.port,
                    },
                    .acc = v,
                };
            }
            if (val_r) |v| {
                res.@"1" = Token{
                    .tag = .{
                        .ip = @intCast(instr.d2.offset + @as(i41, @intCast(from.tag.ip))),
                        .fp = from.tag.fp,
                        .port = instr.d2.port,
                    },
                    .acc = v,
                };
            }
            return res;
        },
        .Switch => {
            if (val_r) |condition| {
                if (val_l) |v| {
                    if (condition != 0) {
                        res.@"0" = Token{
                            .tag = .{
                                .ip = @intCast(instr.d2.offset + @as(i41, @intCast(from.tag.ip))),
                                .fp = from.tag.fp,
                                .port = instr.d2.port,
                            },
                            .acc = v,
                        };
                    } else {
                        res.@"1" = Token{
                            .tag = .{
                                .ip = @intCast(instr.d2.offset + @as(i41, @intCast(from.tag.ip))),
                                .fp = from.tag.fp,
                                .port = instr.d2.port,
                            },
                            .acc = v,
                        };
                    }
                }
            }
            // empty when one of these is missing; should never happen
            return res;
        },
        .Send => {
            if (val_l) |tag| {
                if (val_r) |v| {
                    res.@"0" = .{ .tag = @bitCast(@as(u81, @truncate(tag))), .acc = v };
                    res.@"1" = Token{
                        .tag = .{
                            .ip = @intCast(instr.d1.offset + @as(i41, @intCast(from.tag.ip))),
                            .fp = from.tag.fp,
                            .port = instr.d1.port,
                        },
                        .acc = v,
                    };
                }
            }
            // as before, we should always have both values for this
            return res;
        },
        .Extract => {
            res.@"0" = Token{
                .tag = .{
                    .ip = @intCast(instr.d1.offset + @as(i41, @intCast(from.tag.ip))),
                    .fp = from.tag.fp,
                    .port = instr.d1.port,
                },
                .acc = @intCast(@as(u81, @bitCast(Tag{
                    .ip = @intCast(instr.d2.offset + @as(i41, @intCast(from.tag.ip))),
                    .fp = from.tag.fp,
                    .port = instr.d2.port,
                }))),
            };
            return res;
        },
    }
}
