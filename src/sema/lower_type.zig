// This file contains mechanism of
// AST type -> TypeId.

const std = @import("std");
const ast = @import("../ast.zig");
const types = @import("type_system.zig");
const scope_mod = @import("scope.zig");

const TypeId = types.TypeId;

pub fn resolve(ts: *types.TypeSystem, sc: *scope_mod.Scope, ty: *ast.Type) anyerror!TypeId {
    var id: TypeId = switch (ty.base) {
        .primitive => |p| try ts.from_ast_primitive(p),
        .pointer => |inner| blk: {
            const cid = try resolve(ts, sc, inner);
            break :blk try ts.intern(.{ .pointer = .{ .child = cid } });
        },
        .slice => |*s| blk: {
            const cid = try resolve(ts, sc, s.elem);
            break :blk try ts.intern(.{ .slice = .{ .child = cid } });
        },
        .array => |*a| blk: {
            const cid = try resolve(ts, sc, a.elem);
            // rewriting the ast here, evaluating the expr if we got expr as size
            if (a.size == .expr) {
                const e = a.size.expr;
                const n = const_int(e, sc) orelse break :blk .invalid;
                e.deinit(ts.allocator);
                a.size = .{ .fixed = try std.fmt.allocPrint(ts.arena.allocator(), "{d}", .{n}) };
            }
            break :blk switch (a.size) {
                .fixed => |d| try ts.intern(.{ .array = .{
                    .child = cid,
                    .len = std.fmt.parseInt(u64, d, 10) catch return .invalid,
                } }),
                .expr, .inferred => .invalid,
            };
        },
        .func => |*f| blk: {
            var params: std.ArrayList(TypeId) = .empty;
            errdefer params.deinit(ts.allocator);
            for (f.params.items) |p| try params.append(ts.allocator, try resolve(ts, sc, p));
            const rid = try resolve(ts, sc, f.result);
            break :blk try ts.intern(.{ .function = .{ .params = params, .result = rid } });
        },
        .proc => |*pr| blk: {
            var params: std.ArrayList(TypeId) = .empty;
            errdefer params.deinit(ts.allocator);
            for (pr.params.items) |p| try params.append(ts.allocator, try resolve(ts, sc, p));
            break :blk try ts.intern(.{ .procedure = .{ .params = params } });
        },
        .named => |n| blk: {
            const sym = sc.resolve(n.name) orelse break :blk .invalid;
            break :blk switch (sym.kind) {
                .@"struct", .@"enum", .type_alias => sym.ty,
                else => .invalid,
            };
        },
    };

    if (ty.is_optional) id = try ts.intern(.{ .optional = id });
    if (ty.is_error_union) id = try ts.intern(.{ .error_union = id });
    return id;
}

// for constant expr evaluation at semantics stage
pub fn const_int(e: *ast.Expr, sc: *scope_mod.Scope) ?usize { // as it's for array size I am returning usize
    switch (e.*) {
        .literal => |l| return if (l.kind == .integer) l.ivalue else null,
        .ident => |i| {
            const sym = sc.resolve(i.name) orelse return null;
            return if (sym.kind == .constant) sym.const_val else null;
        },
        .binary => |b| {
            const l = const_int(b.lhs, sc) orelse return null;
            const r = const_int(b.rhs, sc) orelse return null;
            return switch (b.op) {
                .add => std.math.add(u64, l, r) catch null,
                .sub => std.math.sub(u64, l, r) catch null,
                .mul => std.math.mul(u64, l, r) catch null,
                .div => if (r == 0) null else l / r,
                .mod => if (r == 0) null else l % r,
                .shl => if (r >= 64) null else l << @intCast(r),
                .shr => if (r >= 64) null else l >> @intCast(r),
                else => null,
            };
        },
        else => return null,
    }
}
