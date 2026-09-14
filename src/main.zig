const std = @import("std");
const Io = std.Io;

const squall_v2 = @import("squall_v2");

pub fn main(init: std.process.Init) !void {
    var state = squall_v2.State{
        .memory = .init(init.arena.allocator()),
        .stackBase = 0x7FFFFFFF,
        .stackTop = 0x7FFFFFFF,
    };
    state.push(.{ .ip = 0, .fp_repr = 0xFF, .port = .Left, .acc = 1 });
    std.debug.print("{}\n", .{state});
    squall_v2.clock(&state);
    std.debug.print("{}\n", .{state});
}
