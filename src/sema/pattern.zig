// This file contains all the semantics of
// Match-arm patterns.

const std = @import("std");
const ast = @import("../ast.zig");
const types = @import("type_system.zig");
const Sema = @import("semantics.zig").Sema;
const Token = @import("../token.zig").Token;

const TypeId = types.TypeId;

pub fn check(s: *Sema, pat: *ast.Pattern, sty: TypeId, tok: Token) !void {
    if (sty == .invalid) return;
    switch (pat.*) {
        .integer => if (!s.types.literal_fits(.integer, sty)) {
            try s.err("integer pattern can't match a value of type {s}", .{s.types.name_of(sty)}, tok);
        },
        .boolean => if (!s.types.assignable(try s.types.primitive(.bool), sty)) {
            try s.err("bool pattern can't match a value of type {s}", .{s.types.name_of(sty)}, tok);
        },
        .variant => |*v| try check_variant(s, v, sty),
        .field_variant => |e| try check_field_variant(s, e, sty),
        else => {}, // TODO
    }
}

fn check_variant(s: *Sema, v: *ast.VariantPattern, sty: TypeId) !void {
    if (s.types.get(sty).* != .enum_ty) {
        try s.err("variant pattern '{s}' can't match a value of type  {s}", .{ v.name, s.types.name_of(sty) }, v.token);
        return;
    }
    const edef = s.types.get(sty).enum_ty;
    var vname = v.name;
    if (std.mem.lastIndexOfScalar(u8, v.name, '.')) |dot| {
        vname = v.name[dot + 1 ..];
        const ename = v.name[0..dot];
        const sym = s.scope.resolve(ename) orelse {
            try s.err("Unknown identifier: '{s}'", .{ename}, v.token);
            return;
        };
        if ((sym.kind != .@"enum" and sym.kind != .type_alias) or sym.ty != sty) {
            try s.err("type mismatch: expected {s}, found {s}", .{ s.types.name_of(sty), ename }, v.token);
            return;
        }
    }

    for (edef.variants.items) |ev| {
        if (std.mem.eql(u8, ev.name, vname)) return;
    }
    try s.err("enum '{s}' has no variant '{s}'", .{ edef.name, vname }, v.token);
}

fn check_field_variant(s: *Sema, e: *ast.Expr, sty: TypeId) !void {
    if (e.* != .field_access) return;
    const fa = e.field_access;

    const ename = switch (fa.target.*) {
        .ident => |i| i.name,
        else => {
            try s.err("expected enum name before '.'", .{}, fa.token);
            return;
        },
    };
    const vname = switch (fa.field.*) {
        .ident => |i| i.name,
        else => {
            try s.err("expected variant name after '.'", .{}, fa.token);
            return;
        },
    };

    var tmp = ast.VariantPattern{
        .name = try s.qualify(ename, vname),
        .params = .empty,
        .token = fa.token,
    };
    try check_variant(s, &tmp, sty);
}

// the bare variant name of a pattern (`Color.Red` -> `Red`), if it has one
pub fn variant_name(pat: *ast.Pattern) ?[]const u8 {
    return switch (pat.*) {
        .variant => |v| if (std.mem.lastIndexOfScalar(u8, v.name, '.')) |dot| v.name[dot + 1 ..] else v.name,
        .field_variant => |e| if (e.* == .field_access and e.field_access.field.* == .ident) e.field_access.field.ident.name else null,
        else => null,
    };
}
