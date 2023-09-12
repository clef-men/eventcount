const std = @import("std");

const State =
    u64;
const StateSigned =
    i64;

const stack_bitsize: State =
    16;
const stack_mask: State =
    (1 << stack_bitsize) - 1;
inline fn makeStack(stack: State) State {
    return stack;
}
inline fn selectStack(state: State) State {
    return state & stack_mask;
}
inline fn getStack(state: State) State {
    return state & stack_mask;
}
inline fn withStack(state: State, stack: State) State {
    return (state & ~stack_mask) | stack;
}

const waiters_bitsize: State =
    16;
const waiters_shift: State =
    stack_bitsize;
const waiters_incr: State =
    1 << waiters_shift;
const waiters_max: State =
    (1 << waiters_bitsize) - 1;
const waiters_mask: State =
    waiters_max << waiters_shift;
inline fn makeWaiters(waiters: State) State {
    return waiters << waiters_shift;
}
inline fn selectWaiters(state: State) State {
    return state & waiters_mask;
}
inline fn getWaiters(state: State) State {
    return selectWaiters(state) >> waiters_shift;
}

const epoch_bitsize: State =
    32;
const epoch_shift: State =
    waiters_shift + waiters_bitsize;
const epoch_incr: State =
    1 << epoch_shift;
const epoch_mask: State =
    ((1 << epoch_bitsize) - 1) << epoch_shift;
inline fn makeEpoch(epoch: State) State {
    return epoch << epoch_shift;
}
inline fn selectEpoch(state: State) State {
    return state & epoch_mask;
}
inline fn getEpoch(state: State) State {
    return selectEpoch(state) >> epoch_shift;
}

const Waiter = struct {
    const Self = @This();

    const Status = enum {
        not_signaled,
        waiting,
        signaled,
    };

    next: std.atomic.Atomic(?*Self),
    mutex: std.Thread.Mutex,
    condition: std.Thread.Condition,
    state: State,
    status: Status,

    pub fn init() Self {
        return .{
            .next = std.atomic.Atomic(?*Self).init(null),
            .mutex = .{},
            .condition = .{},
            .state = 0,
            .status = .not_signaled,
        };
    }

    pub fn park(self: *Self) void {
        self.mutex.lock();
        defer self.mutex.unlock();

        while (self.status != .signaled) {
            self.status = .waiting;
            self.condition.wait(&self.mutex);
        }
    }
    pub fn unpark(self: ?*Self) void {
        var waiter = self;
        while (waiter) |waiter_| {
            waiter = waiter_.next.load(.Monotonic);
            const status = blk: {
                waiter_.mutex.lock();
                defer waiter_.mutex.unlock();

                const status = waiter_.status;
                waiter_.status = .signaled;
                break :blk status;
            };
            if (status == .waiting) {
                waiter_.condition.signal();
            }
        }
    }
};

pub const Notifier = struct {
    const Self = @This();

    allocator: std.mem.Allocator,
    state: std.atomic.Atomic(State),
    waiters: []Waiter,

    pub fn init(allocator: std.mem.Allocator, n: usize) !Self {
        std.debug.assert(n < waiters_max);

        var waiters = try allocator.alloc(Waiter, n);
        errdefer allocator.free(waiters);
        for (waiters) |*waiter| {
            waiter.* = Waiter.init();
        }

        const state = stack_mask | (epoch_mask - epoch_incr * n * 2);

        return .{
            .allocator = allocator,
            .state = std.atomic.Atomic(State).init(state),
            .waiters = waiters,
        };
    }
    pub export fn deinit(self: *Self) void {
        std.debug.assert(self.state.load(.SeqCst) & (stack_mask | waiters_mask) == stack_mask);

        self.allocator.free(self.waiters);
    }

    pub export fn size(self: *Self) usize {
        return self.waiters.len;
    }

    pub fn get(self: Self, i: usize) *Waiter {
        return &self.waiters[i];
    }
    pub fn index(self: Self, waiter: *Waiter) usize {
        return @intFromPtr(waiter) - @intFromPtr(self.get(0));
    }

    pub export fn prepareWait(self: *Self, waiter: *Waiter) void {
        waiter.state = self.state.fetchAdd(waiters_incr, .Monotonic);
        @fence(.SeqCst);
    }

    pub export fn commitWait(self: *Self, waiter: *Waiter) void {
        waiter.status = .not_signaled;
        const epoch = selectEpoch(waiter.state) + makeEpoch(getWaiters(waiter.state));
        var state = self.state.load(.SeqCst);
        while (true) {
            const delta_epoch = @as(StateSigned, @bitCast(selectEpoch(state) -% epoch));
            if (delta_epoch < 0) {
                std.Thread.yield() catch {};
                state = self.state.load(.SeqCst);
                continue;
            }
            if (0 < delta_epoch) {
                return;
            }
            std.debug.assert(selectWaiters(state) != 0);
            const new_state = withStack(state - waiters_incr + epoch_incr, @intCast(self.index(waiter)));
            if (selectStack(state) == stack_mask) {
                waiter.next.store(null, .Monotonic);
            } else {
                waiter.next.store(self.get(getStack(state)), .Monotonic);
            }
            if (self.state.tryCompareAndSwap(state, new_state, .Release, .Monotonic) == null) {
                waiter.park();
                return;
            }
        }
    }

    pub export fn cancelWait(self: *Self, waiter: *Waiter) void {
        const epoch = selectEpoch(waiter.state) + makeEpoch(getWaiters(waiter.state));
        var state = self.state.load(.Monotonic);
        while (true) {
            const delta_epoch = @as(StateSigned, @bitCast(selectEpoch(state) -% epoch));
            if (delta_epoch < 0) {
                std.Thread.yield() catch {};
                state = self.state.load(.Monotonic);
                continue;
            }
            if (0 < delta_epoch) {
                return;
            }
            std.debug.assert(selectWaiters(state) != 0);
            const new_state = state - waiters_incr + epoch_incr;
            if (self.state.tryCompareAndSwap(state, new_state, .Monotonic, .Monotonic) == null) {
                return;
            }
        }
    }

    pub export fn notify(self: *Self, all: bool) void {
        @fence(.SeqCst);
        const state = self.state.load(.Acquire);
        while (true) {
            if (selectStack(state) == stack_mask and selectWaiters(state) == 0) {
                return;
            }
            const waiters = getWaiters(state);
            const new_state =
                if (all)
                selectEpoch(state) + makeEpoch(waiters) + stack_mask
            else if (waiters != 0)
                state + epoch_incr - waiters_incr
            else blk: {
                const waiter = self.get(getStack(state));
                const next =
                    if (waiter.next.load(.Monotonic)) |next|
                    makeStack(@intCast(self.index(next)))
                else
                    stack_mask;
                break :blk selectEpoch(state) + next;
            };
            if (self.state.tryCompareAndSwap(state, new_state, .Acquire, .Acquire) == null) {
                if ((!all and waiters != 0) or selectStack(state) == stack_mask) {
                    return;
                }
                const waiter = self.get(getStack(state));
                if (!all) {
                    waiter.next.store(null, .Monotonic);
                }
                waiter.unpark();
                return;
            }
        }
    }
    pub export fn notifyOne(self: *Self) void {
        self.notify(false);
    }
    pub export fn notifyAll(self: *Self) void {
        self.notify(true);
    }
    pub export fn notifyMany(self: *Self, n: usize) void {
        if (self.size() <= n) {
            self.notifyAll();
        } else {
            for (0..n) |_| {
                self.notifyOne();
            }
        }
    }
};

test "basic" {
    var notifier = try Notifier.init(std.heap.c_allocator, 8);
    defer notifier.deinit();
}
