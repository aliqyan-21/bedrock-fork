// This file contains all the sema of
// Statements and control flow.

const std = @import("std");
const ast = @import("../ast.zig");
const scope = @import("scope.zig");
const types = @import("type_system.zig");
const Sema = @import("semantics.zig").Sema;
const expr_mod = @import("expr.zig");
const pattern = @import("pattern.zig");
const Token = @import("../token.zig").Token;

const TypeId = types.TypeId;

// does this statement list always leave (return / break / continue on every path)?
pub fn body_returns(stmts: []const ast.Stmt) bool {
    if (stmts.len == 0) return false;
    return switch (stmts[stmts.len - 1]) {
        .return_stmt, .break_stmt, .continue_stmt => true,
        .control_flow_stmt => |cf| switch (cf) {
            .if_expr => |i| blk: {
                const eb = i.else_body orelse break :blk false;
                if (!body_returns(i.then_body.items)) break :blk false;
                for (i.elifs.items) |e| if (!body_returns(e.body.items)) break :blk false;
                break :blk body_returns(eb.items);
            },
            .match_expr => |m| blk: {
                const eb = m.else_body orelse break :blk false;
                for (m.arms.items) |arm| if (!body_returns(arm.body.items)) break :blk false;
                break :blk body_returns(eb.items);
            },
            else => false,
        },
        else => false,
    };
}

// check `stmts` in a fresh child scope
pub fn block(s: *Sema, stmts: []ast.Stmt, kind: scope.Scope.Id) anyerror!void {
    var block_scope = scope.Scope.init(s.compiler.allocator, kind, s.scope);
    defer block_scope.deinit();

    const saved = s.scope;
    s.scope = &block_scope;
    defer s.scope = saved;

    for (stmts, 0..) |*stmt, idx| {
        // only the statement right before can end the block
        if (idx > 0 and body_returns(stmts[idx - 1 .. idx])) {
            if (stmt.token_of()) |tok| {
                try s.err("unreachable code", .{}, tok);
            }
            break;
        }
        try check_stmt(s, stmt);
    }
}

pub fn check_stmt(s: *Sema, stmt: *ast.Stmt) anyerror!void {
    switch (stmt.*) {
        .var_stmt => |*v| try s.check_binding(.variable, v.name, v.type_ann, v.value, v.token),
        .const_stmt => |*c| try s.check_binding(.constant, c.name, c.type_ann, c.value, c.token),
        .local_static_var_stmt => |lv| try s.check_binding(.variable, lv.name, lv.type_ann, lv.value, lv.token),
        .assign_stmt => |*a| try check_assign(s, a.target, a.value, a.token),
        .defer_stmt => |*d| try s.enter_scope(d.statement_list.items, .block),
        .unsafe_stmt => |*u| try s.enter_scope(u.body.items, .unsafe),
        .control_flow_stmt => |*c| try check_control_flow(s, c),
        .return_stmt => |*r| try check_return(s, r.value, r.token),
        .expr_stmt => |*e| {
            if (e.value) |val| try check_expr_stmt(s, val);
        },
        .break_stmt => |*b| try check_loop_jump(s, "break", b.token),
        .continue_stmt => |*c| try check_loop_jump(s, "continue", c.token),
        else => {},
    }
}

fn check_assign(s: *Sema, target: *ast.Expr, value: *ast.Expr, tok: Token) !void {
    if (target.* == .ident and std.mem.eql(u8, target.ident.name, "_")) {
        _ = try s.check_expr(value, null);
        return;
    }
    const tty = try s.check_expr(target, null);
    if (expr_mod.const_root(s, target)) |name| {
        try s.err("cannot assign to constant '{s}'", .{name}, tok);
    }
    const vty = try s.check_expr(value, types.hint(tty));
    if (tty != .invalid and vty != .invalid and !s.types.assignable(vty, tty)) {
        try s.err("type mismatch: expected {s}, found {s}", .{ s.types.name_of(tty), s.types.name_of(vty) }, target.token_of());
    }
}

fn check_return(s: *Sema, value: ?*ast.Expr, tok: Token) !void {
    // note: should we handle nil explicitly ??
    const fn_scope = s.scope.enclosing(.func) orelse {
        try s.err("return used outside of function", .{}, tok);
        if (value) |val| _ = try s.check_expr(val, null);
        return;
    };
    const info = fn_scope.fn_info orelse return;
    switch (info) {
        .func => |rty| {
            const val = value orelse {
                try s.err("return should return a value of type {s}", .{s.types.name_of(rty)}, tok);
                return;
            };
            const vty = try s.check_expr(val, types.hint(rty));
            if (rty != .invalid and !s.types.assignable(vty, rty)) {
                try s.err("type mismatch expected {s}, found {s}", .{ s.types.name_of(rty), s.types.name_of(vty) }, tok);
            }
        },
        .proc => {
            if (value) |val| {
                _ = try s.check_expr(val, null);
                try s.err("proc cannot return a value", .{}, tok);
            }
        },
    }
}

fn check_expr_stmt(s: *Sema, val: *ast.Expr) !void {
    const saved = s.discard;
    s.discard = true;
    defer s.discard = saved;

    const ty = try s.check_expr(val, null);
    // info: func calls must always return a value and proc calls never,
    // and a proc call already yields .invalid, so it is not reported here
    if (ty != .invalid and val.* == .call) {
        try s.err("unused return value: use '_ = ...' to discard", .{}, val.call.token);
    }
}

fn check_loop_jump(s: *Sema, comptime what: []const u8, tok: Token) !void {
    if (s.scope.enclosing(.loop) == null) {
        try s.err(what ++ " used outside of loop", .{}, tok);
    }
}

// --- control flow ---

fn check_control_flow(s: *Sema, stmt: *ast.ControlFlowStmt) !void {
    switch (stmt.*) {
        .if_expr => |*i| try check_if(s, i),
        .match_expr => |*m| try check_match(s, m),
        .while_expr => |*w| {
            _ = try s.check_expr(w.cond, null);
            try s.enter_scope(w.body.items, .loop);
        },
        .for_expr => |*f| try check_for(s, f),
    }
}

fn check_if(s: *Sema, i: anytype) !void {
    _ = try s.check_expr(i.cond, null);
    try s.enter_scope(i.then_body.items, .block);
    for (i.elifs.items) |*e| {
        _ = try s.check_expr(e.cond, null);
        try s.enter_scope(e.body.items, .block);
    }
    if (i.else_body) |*body| {
        try s.enter_scope(body.items, .block);
    }
}

fn check_match(s: *Sema, m: anytype) !void {
    const sty = try s.check_expr(m.subject, null);
    const is_enum = sty != .invalid and s.types.get(sty).* == .enum_ty;

    // using hashmap to track that if all the enum variants are used.
    // could there be a better way to do this?
    var covered = std.StringHashMap(void).init(s.compiler.allocator);
    defer covered.deinit();

    for (m.arms.items) |*arm| {
        try pattern.check(s, &arm.pattern, sty, arm.token);
        if (is_enum) {
            if (pattern.variant_name(&arm.pattern)) |vname| try covered.put(vname, {});
        }
        try s.enter_scope(arm.body.items, .block);
    }

    if (is_enum and m.else_body == null) {
        const edef = s.types.get(sty).enum_ty;
        for (edef.variants.items) |ev| {
            if (!covered.contains(ev.name)) {
                try s.err("enumeration value '{s}' not handled in match", .{ev.name}, m.token);
            }
        }
    }

    if (m.else_body) |*body| {
        try s.enter_scope(body.items, .block);
    }
}

fn check_for(s: *Sema, f: anytype) !void {
    const ity = try s.check_expr(f.iterable, null);
    const elemty: TypeId = if (ity == .invalid) .invalid else switch (s.types.get(ity).*) {
        .range => |r| r.elem,
        .array => |a| a.child,
        .slice => |sl| sl.child,
        else => blk: {
            try s.err("cannot iterate over type {s}", .{s.types.name_of(ity)}, f.token);
            break :blk .invalid;
        },
    };

    // the enumerate start is evaluated in the *outer* scope
    if (f.index_binding != null) {
        const usize_ty = try s.types.primitive(.usize);
        const sty = try s.check_expr(f.index_start.?, usize_ty); // expeting the type of idx to be usize always
        if (sty != .invalid and !s.types.assignable(sty, usize_ty)) {
            try s.err("enumerate start must be usize, found {s}", .{s.types.name_of(sty)}, f.index_start.?.token_of());
        }
    }

    var loop_scope = scope.Scope.init(s.compiler.allocator, .loop, s.scope);
    defer loop_scope.deinit();
    const saved = s.scope;
    s.scope = &loop_scope;
    defer s.scope = saved;

    if (f.index_binding) |ib| {
        try s.declare(.{ .name = ib, .kind = .variable, .ty = try s.types.primitive(.usize) }, f.token);
    }
    try s.declare(.{ .name = f.binding, .kind = .variable, .ty = elemty }, f.token);

    for (f.body.items) |*st| try check_stmt(s, st);
}
