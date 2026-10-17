// expression checking. `check` is just a dispatcher; every form has its own
// small function. (Calls and method lowering are in call.zig.)
// parameters typed `anytype` are the AST payload of that expression form.

const std = @import("std");
const ast = @import("../ast.zig");
const scope = @import("scope.zig");
const types = @import("type_system.zig");
const Sema = @import("semantics.zig").Sema;
const call_mod = @import("call.zig");
const Token = @import("../token.zig").Token;

const TypeId = types.TypeId;

pub fn check(s: *Sema, e: *ast.Expr, expected: ?TypeId) anyerror!TypeId {
    const ty: TypeId = switch (e.*) {
        .literal => |*lit| try check_literal(s, lit.kind, expected),
        .ident => |i| try check_ident(s, i.name, i.token),
        .binary => |*b| try check_binary(s, b, expected),
        .unary => |*u| try check_unary(s, e, u, expected),
        .field_access => |*fa| try check_field_access(s, fa),
        .call => |*c| try call_mod.check_call(s, c),
        .index => |*i| try check_index(s, i),
        .array_literal => |*al| try check_array_literal(s, al, expected),
        .nil => |*n| try check_nil(s, n.token, expected),
        .undefined => try check_undefined(s, e, expected),
        .struct_literal => |*sl| try check_struct_literal(s, sl, expected),
        // these two are not recorded in expr_types
        .optional_unwrap => |*o| {
            _ = try check(s, o.operand, null);
            return .invalid; //todo: optional type
        },
        .comptime_expr => |*ce| {
            try s.enter_scope(ce.body.items, .block);
            return .invalid; //todo: comptime type
        },
    };
    try s.expr_types.put(s.compiler.allocator, e, ty);
    return ty;
}

// the symbol `e` names, if `e` is a plain identifier
pub fn ident_symbol(s: *Sema, e: *ast.Expr) ?scope.Symbol {
    if (e.* != .ident) return null;
    return s.scope.resolve(e.ident.name);
}

// check if expression is lvalue or not
fn is_lvalue(e: *ast.Expr) bool {
    return switch (e.*) {
        .ident, .field_access, .index => true,
        .unary => |u| u.op == .deref,
        else => false,
    };
}

// to find if the expression a place stored inline in an array for now
// todo: could be expanded to structs, slice, etc.
fn is_inline_value(s: *Sema, e: *ast.Expr) bool {
    const t = s.expr_types.get(e) orelse return false;
    if (t == .invalid) return false;
    return switch (s.types.get(t).*) {
        .array => true,
        else => false,
    };
}

// to find name of const owning this place
pub fn const_root(s: *Sema, e: *ast.Expr) ?[]const u8 {
    return switch (e.*) {
        .ident => |i| blk: {
            const sym = s.scope.resolve(i.name) orelse break :blk null;
            break :blk if (sym.kind == .constant) sym.name else null;
        },
        .field_access => |f| if (is_inline_value(s, f.target)) const_root(s, f.target) else null,
        .index => |i| if (is_inline_value(s, i.target)) const_root(s, i.target) else null,
        else => null,
    };
}

// --- leaves ---

fn check_literal(s: *Sema, kind: ast.LiteralKind, expected: ?TypeId) !TypeId {
    if (expected) |exp| {
        if (s.types.literal_fits(kind, exp)) return exp;
    }
    return s.types.literal_type(kind);
}

fn check_ident(s: *Sema, name: []const u8, tok: Token) !TypeId {
    const sym = s.scope.resolve(name) orelse {
        try s.err("Unknown identifier '{s}'", .{name}, tok);
        return .invalid;
    };
    return sym.ty;
}

fn check_nil(s: *Sema, tok: Token, expected: ?TypeId) !TypeId {
    if (expected) |exp| {
        const fits = switch (s.types.get(exp).*) {
            .optional => true,
            .error_union => |inner| s.types.get(inner).* == .optional,
            else => false,
        };
        if (fits) return exp;
    }
    try s.err("cannot infer type of nil without context", .{}, tok);
    return .invalid;
}

fn check_undefined(s: *Sema, e: *ast.Expr, expected: ?TypeId) !TypeId {
    if (expected) |exp| return exp;
    try s.err("cannot infer type of 'undefined' without context", .{}, e.token_of());
    return .invalid;
}

// --- binary ---

fn check_binary(s: *Sema, b: anytype, expected: ?TypeId) anyerror!TypeId {
    switch (b.op) {
        .range, .range_incl => return check_range(s, b, expected),
        .orelse_op => return .invalid, //todo: oresle unwrap
        .logical_and, .logical_or => return check_logical(s, b),
        else => {},
    }

    const is_comparison = switch (b.op) {
        .eq, .ne, .lt, .gt, .le, .ge => true,
        else => false,
    };

    // implicit type conversion (numeric widening) is allowed for now
    // those who need explicit type conversion give error here
    var lty: TypeId = undefined;
    var rty: TypeId = undefined;
    if (expected == null and b.lhs.* == .literal and b.rhs.* != .literal) {
        // let the non-literal side decide the literal's type
        rty = try check(s, b.rhs, null);
        lty = try check(s, b.lhs, types.hint(rty));
    } else {
        lty = try check(s, b.lhs, expected);
        rty = try check(s, b.rhs, expected orelse types.hint(lty));
    }

    const result_ty = s.types.unify(lty, rty) orelse {
        try s.err("type mismatch in binary expression {s} and {s}", .{ s.types.name_of(lty), s.types.name_of(rty) }, b.token);
        return .invalid;
    };
    return if (is_comparison) try s.types.primitive(.bool) else result_ty;
}

fn check_range(s: *Sema, b: anytype, expected: ?TypeId) !TypeId {
    const lty = try check(s, b.lhs, expected);
    const rty = try check(s, b.rhs, expected orelse types.hint(lty));
    const elemty = s.types.unify(lty, rty) orelse {
        try s.err("range bounds must have the same type: {s} and {s}", .{ s.types.name_of(lty), s.types.name_of(rty) }, b.token);
        return .invalid;
    };
    if (elemty == .invalid) return .invalid;
    return s.types.intern(.{ .range = .{ .elem = elemty } });
}

fn check_logical(s: *Sema, b: anytype) !TypeId {
    const boolty = try s.types.primitive(.bool);
    const lty = try check(s, b.lhs, boolty);
    const rty = try check(s, b.rhs, boolty);
    if (lty != .invalid and !s.types.assignable(lty, boolty)) {
        try s.err("expected bool, found {s}", .{s.types.name_of(lty)}, b.lhs.token_of());
    }
    if (lty != .invalid and !s.types.assignable(rty, boolty)) {
        try s.err("expected bool, found {s}", .{s.types.name_of(rty)}, b.rhs.token_of());
    }
    return boolty;
}

// --- unary ---

fn check_unary(s: *Sema, e: *ast.Expr, u: anytype, expected: ?TypeId) !TypeId {
    return switch (u.op) {
        .neg => try unary_neg(s, u, expected),
        .not => try unary_not(s, u),
        .bit_not => try unary_bit_not(s, u, expected),
        .addr_of => try unary_addr_of(s, e, u),
        .deref => try unary_deref(s, u),
        .new => blk: {
            const ty = try check(s, u.operand, null);
            if (ty == .invalid) break :blk .invalid;
            break :blk try s.types.intern(.{ .pointer = .{ .child = ty } });
        },
    };
}

fn unary_neg(s: *Sema, u: anytype, expected: ?TypeId) !TypeId {
    const ty = try check(s, u.operand, expected);
    if (ty == .invalid) return .invalid;
    if (s.types.is_unsigned(ty)) {
        try s.err("cannot negate value of unsiged type {s}", .{s.types.name_of(ty)}, u.token);
        return .invalid;
    }
    if (!s.types.is_numeric(ty)) {
        try s.err("cannot negate non-numeric type {s}", .{s.types.name_of(ty)}, u.token);
    }
    return ty;
}

fn unary_not(s: *Sema, u: anytype) !TypeId {
    const boolty = try s.types.primitive(.bool);
    const ty = try check(s, u.operand, boolty);
    if (ty != .invalid and !s.types.assignable(ty, boolty)) {
        try s.err("expected a bool, but found {s}", .{s.types.name_of(ty)}, u.token);
    }
    return boolty;
}

fn unary_bit_not(s: *Sema, u: anytype, expected: ?TypeId) !TypeId {
    const ty = try check(s, u.operand, expected);
    if (ty != .invalid and !s.types.is_integer(ty)) {
        try s.err("cannot bitwise-not non-integer type {s}", .{s.types.name_of(ty)}, u.token);
    }
    return ty;
}

fn unary_addr_of(s: *Sema, e: *ast.Expr, u: anytype) !TypeId {
    if (!is_lvalue(u.operand)) {
        try s.err("cannot take address of a non-lvalue expression", .{}, u.token);
        return .invalid;
    }
    const innerty = try check(s, u.operand, null);
    // (already recorded => this is a re-visit, the error was reported the first time)
    if (!s.expr_types.contains(e)) {
        if (const_root(s, u.operand)) |name| {
            try s.err("cannot take the address of constant '{s}'", .{name}, u.token);
        }
    }
    if (innerty == .invalid) return .invalid;
    return s.types.intern(.{ .pointer = .{ .child = innerty } });
}

fn unary_deref(s: *Sema, u: anytype) !TypeId {
    const ty = try check(s, u.operand, null);
    if (ty == .invalid) return .invalid;
    switch (s.types.get(ty).*) {
        .pointer => |p| return p.child,
        else => {
            try s.err("cannot dereference non pointer type {s}", .{s.types.name_of(ty)}, u.token);
            return .invalid;
        },
    }
}

// --- field access / index ---

fn check_field_access(s: *Sema, fa: anytype) !TypeId {
    const tty = try check(s, fa.target, null);
    if (tty == .invalid) return .invalid;

    const stty = s.types.struct_of(tty);
    const field = switch (fa.field.*) {
        .ident => |id| id.name,
        else => return .invalid,
    };

    if (stty == .invalid) {
        try s.err("cannot access field '{s}' on non-struct and non-enum type '{s}'", .{ field, s.types.name_of(tty) }, fa.token);
        return .invalid;
    }

    switch (s.types.get(stty).*) {
        .struct_ty => |sdef| {
            for (sdef.fields.items) |sf| {
                if (std.mem.eql(u8, sf.name, field)) return sf.ty;
            }
            try s.err("struct '{s}' has no field '{s}'", .{ sdef.name, field }, fa.token);
            return .invalid;
        },
        .enum_ty => |edef| {
            for (edef.variants.items) |ef| {
                if (!std.mem.eql(u8, ef.name, field)) continue;

                // enum.Variant (named through the type itself) is the enum value
                const via_type = if (ident_symbol(s, fa.target)) |sym| sym.kind == .@"enum" else false;
                if (via_type) return tty;

                // otherwise it reads the variant's payload
                switch (ef.types.items.len) {
                    0 => {
                        try s.err("variant '{s}' of enum '{s}' has no payload to read", .{ ef.name, edef.name }, fa.token);
                        return .invalid;
                    },
                    1 => return ef.types.items[0],
                    else => {
                        // todo: could implement destructarizing multiple fields in multiple vars
                        try s.err("variant '{s}' carries {d} values and can't be read as a single field", .{ ef.name, ef.types.items.len }, fa.token);
                        return .invalid;
                    },
                }
            }
            try s.err("enum '{s}' has no field '{s}'", .{ edef.name, field }, fa.token);
            return .invalid;
        },
        else => return .invalid,
    }
}

fn check_index(s: *Sema, i: anytype) !TypeId {
    const tty = try check(s, i.target, null);
    for (i.args.items) |arg| _ = try check(s, arg, null);

    if (i.args.items.len != 1) return .invalid; //todo: generics
    if (tty == .invalid) return .invalid;

    switch (s.types.get(tty).*) {
        .array => |a| {
            try check_const_bounds(s, i.args.items[0], a.len);
            return a.child;
        },
        .slice => |sl| return sl.child,
        else => {
            try s.err("cannot index type {s}", .{s.types.name_of(tty)}, i.token);
            return .invalid;
        },
    }
}

// note: bound check is only for constants (which are known during comptime)
fn check_const_bounds(s: *Sema, idx: *ast.Expr, len: u64) !void {
    const is_neg = idx.* == .unary and idx.unary.op == .neg;
    const lit: *ast.LiteralExpr = if (idx.* == .literal)
        &idx.literal
    else if (is_neg and idx.unary.operand.* == .literal)
        &idx.unary.operand.literal
    else
        return;

    if (lit.kind != .integer) return;
    const n = lit.ivalue;
    if (is_neg) {
        try s.err("index -{d} out of bounds of array of length {d}", .{ n, len }, idx.token_of());
    } else if (n >= len) {
        try s.err("index {d} out of bounds of array of length {d}", .{ n, len }, idx.token_of());
    }
}

// ── literals with structure ─────────────────────────────────────────────

// note: if [1,2,3] becomes i32, and if we have [1,2,3,4.5] it gives error, so if
// want floats array have to do explicitly 'const a = [1.0, 2.0, 3.0]'
fn check_array_literal(s: *Sema, al: anytype, expected: ?TypeId) !TypeId {
    const elem_hint: ?TypeId = if (expected) |exp| switch (s.types.get(exp).*) {
        .array => |a| a.child,
        .slice => |sl| sl.child,
        else => null,
    } else null;

    if (al.elements.items.len == 0) {
        if (elem_hint) |h| return s.types.intern(.{ .array = .{ .child = h, .len = 0 } });
        try s.err("cannot infer type or size of empty array literal", .{}, al.token);
        return .invalid;
    }

    var elemty: TypeId = elem_hint orelse .invalid;

    for (al.elements.items) |elem| {
        const want: ?TypeId = elem_hint orelse types.hint(elemty);
        const ety = try check(s, elem, want);
        if (ety == .invalid) continue;
        if (elem_hint == null) {
            elemty = s.types.unify(elemty, ety) orelse {
                try s.err("array elements must have the same type: expected {s}, found {s}", .{ s.types.name_of(elemty), s.types.name_of(ety) }, al.token);
                return .invalid;
            };
            continue;
        }
        if (!s.types.assignable(ety, elemty)) {
            try s.err("array elements must have the same type: expected {s}, found {s}", .{ s.types.name_of(elemty), s.types.name_of(ety) }, al.token);
        }
    }

    if (elemty == .invalid) return .invalid;
    return s.types.intern(.{ .array = .{ .child = elemty, .len = @intCast(al.elements.items.len) } });
}

fn check_struct_literal(s: *Sema, sl: anytype, expected: ?TypeId) !TypeId {
    var stty: TypeId = .invalid;
    if (std.mem.eql(u8, sl.name, "_")) {
        if (expected) |exp| {
            if (s.types.get(exp).* == .struct_ty) stty = exp;
        }
        if (stty == .invalid) {
            try s.err("cannot infer struct type: no target type available", .{}, sl.token);
            return .invalid;
        }
    } else {
        const sym = s.scope.resolve(sl.name) orelse {
            try s.err("unknown type '{s}'", .{sl.name}, sl.token);
            return .invalid;
        };
        if (sym.kind != .@"struct") {
            try s.err("'{s}' is not a struct type", .{sl.name}, sl.token);
            return .invalid;
        }
        stty = sym.ty;
    }

    const sdef = s.types.get(stty).struct_ty;
    var seen = std.StringHashMap(void).init(s.compiler.allocator);
    defer seen.deinit();

    for (sl.field_inits.items) |*fi| {
        var field_ty: ?TypeId = null;
        for (sdef.fields.items) |f| {
            if (std.mem.eql(u8, f.name, fi.name)) {
                field_ty = f.ty;
                break;
            }
        }
        const fty = field_ty orelse {
            try s.err("struct '{s}' has no field '{s}'", .{ sdef.name, fi.name }, fi.token);
            _ = try check(s, fi.value, null);
            continue;
        };

        const slot = try seen.getOrPut(fi.name);
        if (slot.found_existing) {
            try s.err("field '{s}' is initialized more than one time", .{fi.name}, fi.token);
        }

        const vty = try check(s, fi.value, fty);
        if (vty != .invalid and !s.types.assignable(vty, fty)) {
            try s.err("type mismatch for field '{s}': expected {s}, found {s}", .{ fi.name, s.types.name_of(fty), s.types.name_of(vty) }, fi.token);
        }
    }

    for (sdef.fields.items) |f| {
        if (!seen.contains(f.name)) {
            try s.err("uninitialized field '{s}' in struct literal for '{s}'", .{ f.name, sdef.name }, sl.token);
        }
    }
    return stty;
}
