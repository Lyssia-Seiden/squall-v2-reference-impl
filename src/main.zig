const std = @import("std");
const Io = std.Io;

const squall_v2 = @import("root.zig");

pub fn main(init: std.process.Init) !void {
    var state = squall_v2.State{
        .memory = .init(init.arena.allocator()),
        .stackBase = 0x7FFFFFFF,
        .stackTop = 0x7FFFFFFF,
    };
    state.push(.{
        .tag = .init(8, try squall_v2.AlignedSqPtr(3).parse(0xF0), .Left),
        .acc = 1,
    });
    state.write(squall_v2.Instr, 8, .{
        .addr = .{ .signed = 0 },
        .addr_tag = .FrameRelative,
        .token_matching_rule = .Monadic,
        .alu_op = .add,
        .token_forming_rule = .Arith,
        .d1 = .{ .port = .Left, .offset = 8 },
        .d2 = .{ .port = .Left, .offset = -8 },
    });
    state.write(squall_v2.Instr, 16, .{
        .addr = .{ .unsigned = 24 },
        .addr_tag = .Absolute,
        .token_matching_rule = .ConstDyadic,
        .alu_op = .add,
        .token_forming_rule = .Arith,
        .d1 = .{ .port = .Left, .offset = -8 },
        .d2 = .{ .port = .Left, .offset = -16 },
    });
    state.write(squall_v2.MemValue, 24, .{ .pb = .Constant, .val = 0 });
    std.debug.print("{}\n", .{state});
    for (0..256) |_| {
        squall_v2.clock(&state);
        // std.debug.print("{}\n", .{@as(squall_v2.Token, @bitCast(state.read(squall_v2.Token, state.stackTop - @sizeOf(squall_v2.Token))))});
    }
    std.debug.print("{}\n", .{state});
    std.debug.print("{}\n", .{@as(squall_v2.Token, @bitCast(state.read(squall_v2.Token, state.stackBase)))});
}
