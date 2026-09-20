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
        .tag = .init(try .parse(0x8), try squall_v2.AlignedSqPtr(3).parse(0xF0), .Left),
        .acc = 1,
    });
    state.write(squall_v2.Instr, 8, .{
        .tag = .Monadic,
        .data = .{ .monadic = .{
            .alu_op = .Shl,
            .d = .{ .port = .Left, .offset = 1 },
            .send_second_token = false,
            .second_token_port = undefined,
            .imm = 1,
        } },
    });
    state.write(squall_v2.Instr, 16, .{
        .tag = .Monadic,
        .data = .{ .monadic = .{
            .alu_op = .Add,
            .d = .{ .port = .Left, .offset = -1 },
            .send_second_token = false,
            .second_token_port = undefined,
            .imm = 1,
        } },
    });
    std.debug.print("{}\n", .{state});
    for (0..8) |_| {
        squall_v2.clock(&state);
        // std.debug.print("{}\n", .{@as(squall_v2.Token, @bitCast(state.read(squall_v2.Token, state.stackTop - @sizeOf(squall_v2.Token))))});
    }
    std.debug.print("{}\n", .{state});
    std.debug.print("{}\n", .{@as(squall_v2.Token, @bitCast(state.read(squall_v2.Token, state.stackBase)))});
}
