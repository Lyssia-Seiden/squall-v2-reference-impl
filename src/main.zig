const std = @import("std");
const Io = std.Io;

const squall_v2 = @import("root.zig");
const a = @import("assembler.zig");

pub fn main(init: std.process.Init) !void {
    var instrs: a.SqAsm = try .initCapacity(init.arena.allocator(), 128);
    instrs.appendAssumeCapacity(.{
        .label = "double",
        .value = .{ .monadic = .{
            .d = .{ .node = .{ .label = "plus1", .port = .Left } },
            .op = .Shl,
            .imm = 2,
            .second = null,
        } },
    });
    instrs.appendAssumeCapacity(.{
        .label = "plus1",
        .value = .{ .monadic = .{
            .d = .{ .node = .{ .label = "double", .port = .Left } },
            .op = .Add,
            .imm = 1,
            .second = null,
        } },
    });

    var state = try a.create_image(
        init.arena.allocator(),
        instrs,
        &.{},
        0x7FFFFF,
    );
    state.push(.{
        .tag = .init(try .parse(0x8), try squall_v2.AlignedSqPtr(3).parse(0xF0), .Left),
        .acc = 1,
    });
    std.debug.print("{}\n", .{state});
    for (0..8) |_| {
        squall_v2.clock(&state);
        // std.debug.print("{}\n", .{@as(squall_v2.Token, @bitCast(state.read(squall_v2.Token, state.stackTop - @sizeOf(squall_v2.Token))))});
    }
    std.debug.print("{}\n", .{state});
    std.debug.print("{}\n", .{@as(squall_v2.Token, @bitCast(state.read(squall_v2.Token, state.stackBase)))});
}
