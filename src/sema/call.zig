// this file contains semantics of
// calls, and method-call lowering (`p.foo(a)` -> `P.foo(p, a)`).

const std = @import("std");
const ast = @import("../ast.zig");
const scope = @import("scope.zig");
const types = @import("type_system.zig");
const Sema = @import("semantics.zig").Sema;
const expr_mod = @import("expr.zig");

const TypeId = types.TypeId;

/// what a call needs to know about its callee's type
const Signature = struct {
    params: []const TypeId,
    result: TypeId, // unused for procs
    is_proc: bool,
    is_variadic: bool,
};

fn signature_of(s: *Sema, ty: TypeId) ?Signature {
    if (ty == .invalid) return null;
    return switch (s.types.get(ty).*) {
        .function => |f| .{ .params = f.params.items, .result = f.result, .is_proc = false, .is_variadic = f.is_variadic },
        .procedure => |p| .{ .params = p.params.items, .result = .invalid, .is_proc = true, .is_variadic = p.is_variadic },
        else => null,
    };
}

pub fn check_call(s: *Sema, c: *ast.CallExpr) anyerror!TypeId {
    // (the flag is consumed here and not restored, so calls
    // nested in the arguments never count as discarded)
    const discarded = s.discard;
    s.discard = false;

    if (c.callee.* == .field_access and try lower_method_call(s, c)) return .invalid;

    const cty = try s.check_expr(c.callee, null);
    const sig = signature_of(s, cty) orelse {
        for (c.args.items) |arg| _ = try s.check_expr(arg.value, null);
        if (cty != .invalid) {
            try s.err("cannot call non-function type {s}", .{s.types.name_of(cty)}, c.token);
        }
        return .invalid;
    };

    try check_args(s, c, sig);

    if (!sig.is_proc) return sig.result;
    if (!discarded) {
        try s.err("the call is of a proc, and there's no return value to store", .{}, c.token);
    }
    return .invalid;
}

// each argument is checked exactly once: against its parameter type when the
// count matches, otherwise just on its own
fn check_args(s: *Sema, c: *ast.CallExpr, sig: Signature) !void {
    const args = c.args.items;

    if (!sig.is_variadic and args.len == sig.params.len) {
        for (args, sig.params) |arg, pty| {
            const aty = try s.check_expr(arg.value, types.hint(pty));
            if (aty != .invalid and !s.types.assignable(aty, pty)) {
                try s.err("type mismatch: expected {s}, found {s}", .{ s.types.name_of(pty), s.types.name_of(aty) }, c.token);
            }
        }
        return;
    }

    for (args) |arg| _ = try s.check_expr(arg.value, null);
    if (sig.is_variadic) {
        if (args.len < sig.params.len) {
            try s.err("expected atleast {d} arguments, found {d}", .{ sig.params.len, args.len }, c.token);
        }
    } else {
        try s.err("expected {d} arguments, found {d}", .{ sig.params.len, args.len }, c.token);
    }
}

// --- method calls ---

fn params_of(s: *Sema, fnty: TypeId) ?[]const TypeId {
    return switch (s.types.get(fnty).*) {
        .function => |f| f.params.items,
        .procedure => |p| p.params.items,
        else => null,
    };
}

// method is dot callable only if it's first param is the struct (owner)
fn takes_receiver(s: *Sema, fnty: TypeId, owner: TypeId) bool {
    const params = params_of(s, fnty) orelse return false;
    if (params.len == 0 or params[0] == .invalid) return false;
    const p0 = params[0];
    return p0 == owner or (s.types.get(p0).* == .pointer and s.types.get(p0).pointer.child == owner);
}

// auto & and auto * so receiver matches the method's first param
fn receiver_arg(s: *Sema, target: *ast.Expr, tty: TypeId, fnty: TypeId) !*ast.Expr {
    const first = (params_of(s, fnty) orelse unreachable)[0];
    const wants_ptr = s.types.get(first).* == .pointer;
    const is_ptr = s.types.get(tty).* == .pointer;
    if (wants_ptr == is_ptr) return target;

    const e = try s.compiler.allocator.create(ast.Expr);
    e.* = .{ .unary = .{ .op = if (wants_ptr) .addr_of else .deref, .operand = target, .token = target.token_of() } };
    return e;
}

// rewrites P.foo(a) into a plain call to symbol "P.foo", so normal call
// checking does the method work too for us! (this mutates the AST)
// returns true when the call is fully handled (an error was reported).
fn lower_method_call(s: *Sema, c: *ast.CallExpr) anyerror!bool {
    const fa = c.callee.field_access;
    const mname = switch (fa.field.*) {
        .ident => |i| i.name,
        else => return false,
    };

    // `Type.method(...)` (static) or `value.method(...)`
    const type_sym: ?scope.Symbol = blk: {
        const sym = expr_mod.ident_symbol(s, fa.target) orelse break :blk null;
        break :blk if (sym.kind == .@"struct" or sym.kind == .@"enum") sym else null;
    };
    const via_type = type_sym != null;

    var owner: TypeId = .invalid;
    var tty: TypeId = .invalid;
    if (type_sym) |sym| {
        owner = sym.ty;
    } else {
        tty = try s.check_expr(fa.target, null);
        if (tty == .invalid) return true;
        owner = s.types.struct_of(tty);
        if (owner == .invalid) return false;
    }

    const qname = try s.qualify(s.types.name_of(owner), mname);
    const sym = s.scope.resolve(qname) orelse {
        if (!via_type) return false;
        if (s.types.get(owner).* == .enum_ty) {
            try s.err("enum '{s}' has no variant '{s}'", .{ s.types.name_of(owner), mname }, fa.token);
        } else {
            try s.err("struct '{s}' has no method '{s}'", .{ s.types.name_of(owner), mname }, fa.token);
        }
        return true;
    };

    if (!via_type) {
        if (!takes_receiver(s, sym.ty, owner)) {
            try s.err("'{s}' is a static method; call it as {s}.{s}(...)", .{ mname, s.types.name_of(owner), mname }, fa.token);
            return true;
        }
        const recv = try receiver_arg(s, fa.target, tty, sym.ty);
        try c.args.insert(s.compiler.allocator, 0, .{ .value = recv });
    }

    fa.field.deinit(s.compiler.allocator);
    if (via_type) fa.target.deinit(s.compiler.allocator);

    c.callee.* = .{ .ident = .{ .name = qname, .token = fa.token } };
    return false;
}
