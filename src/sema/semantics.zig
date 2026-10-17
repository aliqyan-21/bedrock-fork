// Item rule of thumb:  declare_*  = build the signature / type and put it in scope
//                      check_*    = check the body against that signature

const std = @import("std");
const ast = @import("../ast.zig");
const compiler = @import("../compiler.zig");
const scope = @import("scope.zig");
const types = @import("type_system.zig");
const lower_type = @import("lower_type.zig");
const expr_mod = @import("expr.zig");
const stmt_mod = @import("stmt.zig");
const Token = @import("../token.zig").Token;

const TypeId = types.TypeId;

pub const Sema = struct {
    compiler: *compiler.Compiler,
    scope: *scope.Scope,
    types: types.TypeSystem,
    expr_types: std.AutoHashMapUnmanaged(*ast.Expr, types.TypeId) = .{},
    discard: bool = false, // this is for dicarded values check, like in proc

    pub fn init(c: *compiler.Compiler) Sema {
        return .{
            .compiler = c,
            .scope = undefined,
            .types = types.TypeSystem.init(c.allocator),
            .expr_types = .{},
        };
    }

    pub fn deinit(self: *Sema) void {
        self.types.deinit();
        self.expr_types.deinit(self.compiler.allocator);
    }

    pub fn analyze(self: *Sema) !void {
        var root = scope.Scope.init(self.compiler.allocator, .root, null);
        defer root.deinit();
        self.scope = &root;
        const tree = &self.compiler.ast;

        for (tree.program.items.items) |*item| {
            try self.visit_item(item);
        }
    }

    // --- helpers shared by every sema file ---

    pub fn err(self: *Sema, comptime fmt: []const u8, args: anytype, tok: Token) !void {
        try self.compiler.add_sem_error(fmt, args, .Error, tok);
    }

    pub fn warn(self: *Sema, comptime fmt: []const u8, args: anytype, tok: Token) !void {
        try self.compiler.add_sem_error(fmt, args, .Warn, tok);
    }

    // declare in the current scope.
    // reports "Duplicate <what>: name" on a clash
    pub fn declare_as(self: *Sema, comptime what: []const u8, sym: scope.Symbol, tok: Token) !void {
        self.scope.declare(sym) catch |e| switch (e) {
            error.DuplicateName => try self.err("Duplicate " ++ what ++ ": {s}", .{sym.name}, tok),
            else => return e,
        };
    }

    pub fn declare(self: *Sema, sym: scope.Symbol, tok: Token) !void {
        try self.declare_as("declaration", sym, tok);
    }

    // just turn struct and field to struct.field
    pub fn qualify(self: *Sema, owner: []const u8, name: []const u8) ![]const u8 {
        return std.fmt.allocPrint(self.types.arena.allocator(), "{s}.{s}", .{ owner, name });
    }

    pub fn resolve_type(self: *Sema, ty: *ast.Type) !TypeId {
        return lower_type.resolve(&self.types, self.scope, ty);
    }

    // thin entry points so other sema files don't import each other's internals
    pub fn check_expr(self: *Sema, e: *ast.Expr, expected: ?TypeId) anyerror!TypeId {
        return expr_mod.check(self, e, expected);
    }

    pub fn check_stmt(self: *Sema, st: *ast.Stmt) anyerror!void {
        return stmt_mod.check_stmt(self, st);
    }

    // check `stmts` inside a fresh child scope of the given kind
    pub fn enter_scope(self: *Sema, stmts: []ast.Stmt, kind: scope.Scope.Id) anyerror!void {
        return stmt_mod.block(self, stmts, kind);
    }

    // --- bindings: var / const / static, at top level and inside bodies ---

    fn check_undefined_array_infer(type_ann: ?*ast.Type, value: *ast.Expr) bool {
        if (type_ann) |ty| if (ty.base == .array and ty.base.array.size == .inferred and value.* == .undefined) {
            return true;
        };
        return false;
    }

    pub fn check_binding(
        self: *Sema,
        comptime kind: scope.SymbolKind, // .variable or .constant
        name: []const u8,
        type_ann: ?*ast.Type,
        value: *ast.Expr,
        tok: Token,
    ) !void {
        const what = comptime if (kind == .constant) "constant" else "variable";

        const dty: TypeId = if (type_ann) |ty| blk: {
            const t = try self.resolve_type(ty);
            const inferred = ty.base == .array and ty.base.array.size == .inferred;
            if (t == .invalid and !inferred) {
                try self.err("unknown type for " ++ what ++ " '{s}'", .{name}, ty.token);
            }
            break :blk t;
        } else .invalid;

        if (kind == .constant and value.* == .undefined) {
            try self.err("constant '{s}' cannot be 'undefined'", .{name}, tok);
        }

        const aty: TypeId = if (check_undefined_array_infer(type_ann, value)) blk: {
            try self.err("cannot infer array length: 'undefined' has no length to infer from", .{}, tok);
            break :blk .invalid;
        } else try self.check_expr(value, types.hint(dty));

        if (dty != .invalid and aty != .invalid and !self.types.assignable(aty, dty)) {
            try self.err("type mismatch: expected {s}, found {s}", .{ self.types.name_of(dty), self.types.name_of(aty) }, tok);
        }

        try self.declare(.{
            .name = name,
            .kind = kind,
            .ty = if (dty != .invalid) dty else aty,
            .const_val = if (kind == .constant) lower_type.const_int(value, self.scope) else null,
        }, tok);
    }

    // --- signatures ---

    // resolve parameter types (params: slice of the AST param type)
    fn param_types(self: *Sema, params: anytype) !std.ArrayList(TypeId) {
        var out: std.ArrayList(TypeId) = .empty;
        errdefer out.deinit(self.compiler.allocator);
        for (params) |*param| {
            const pty = try self.resolve_type(param.type);
            if (pty == .invalid) {
                try self.err("unknown type for parameter '{s}'", .{param.name}, param.token);
            }
            try out.append(self.compiler.allocator, pty);
        }
        return out;
    }

    fn func_type(
        self: *Sema,
        params: anytype,
        result: *ast.Type,
        name: []const u8,
        comptime what: []const u8, // "function" / "extern func", only used in the error text
        result_tok: Token,
        is_variadic: bool,
    ) !TypeId {
        var ptys = try self.param_types(params);
        errdefer ptys.deinit(self.compiler.allocator);
        const rty = try self.resolve_type(result);
        if (rty == .invalid) {
            try self.err("unknown return type for " ++ what ++ " '{s}'", .{name}, result_tok);
        }
        return self.types.intern(.{ .function = .{ .params = ptys, .result = rty, .is_variadic = is_variadic } });
    }

    fn proc_type(self: *Sema, params: anytype, is_variadic: bool) !TypeId {
        var ptys = try self.param_types(params);
        errdefer ptys.deinit(self.compiler.allocator);
        return self.types.intern(.{ .procedure = .{ .params = ptys, .is_variadic = is_variadic } });
    }

    fn declare_func(self: *Sema, f: *ast.FunctionDef, name: []const u8) !TypeId {
        const fnty = try self.func_type(f.params.items, f.result, name, "function", f.result.token, false);
        try self.declare(.{ .name = name, .kind = .func, .ty = fnty }, f.token);
        return fnty;
    }

    fn declare_proc(self: *Sema, p: *ast.ProcDef, name: []const u8) !TypeId {
        const prty = try self.proc_type(p.params.items, false);
        try self.declare(.{ .name = name, .kind = .func, .ty = prty }, p.token);
        return prty;
    }

    fn declare_extern(self: *Sema, e_def: anytype) !void {
        switch (e_def.kind) {
            .func => |f| {
                const fnty = try self.func_type(f.params.items, f.result, f.name, "extern func", e_def.token, f.is_variadic);
                try self.declare(.{ .name = f.name, .kind = .func, .ty = fnty }, e_def.token);
            },
            .proc => |p| {
                const prty = try self.proc_type(p.params.items, p.is_variadic);
                try self.declare(.{ .name = p.name, .kind = .func, .ty = prty }, e_def.token);
            },
        }
    }

    // --- type definitions ---

    fn declare_struct(self: *Sema, s: *ast.StructDef) !void {
        const alloc = self.compiler.allocator;
        var field_tys: std.ArrayList(types.StFieldTy) = .empty;
        errdefer field_tys.deinit(alloc);
        for (s.fields.items) |*s_f| {
            const fty = try self.resolve_type(s_f.type);
            if (fty == .invalid) {
                try self.err("unknown type for field '{s}'", .{s_f.name}, s_f.token);
            }
            try field_tys.append(alloc, .{ .name = s_f.name, .ty = fty });
        }

        const sty = try self.types.intern(.{ .struct_ty = .{ .name = s.name, .fields = field_tys } });
        try self.types.register(s.name, sty);
        try self.declare(.{ .name = s.name, .kind = .@"struct", .ty = sty }, s.token);
    }

    fn check_duplicate_fields(self: *Sema, s: *ast.StructDef) !void {
        var seen = std.StringHashMap(void).init(self.compiler.allocator);
        defer seen.deinit();
        for (s.fields.items) |f| {
            const slot = try seen.getOrPut(f.name);
            if (slot.found_existing) {
                try self.err("Duplicate struct field: {s}", .{f.name}, s.token);
            }
        }
    }

    // checks if method and field name clashes and give errors
    fn check_method_clash(self: *Sema, s: *ast.StructDef, name: []const u8, tok: Token) !void {
        for (s.fields.items) |f| {
            if (std.mem.eql(u8, f.name, name)) {
                try self.err("method '{s}' clashes with the field of the same name", .{name}, tok);
            }
        }
    }

    // in two passes we first declare the signature
    // of all methods in struct (so methods can call
    // each other in any order) then again we do pass
    // and this time we visit the bodies of methods.
    fn visit_methods(self: *Sema, s: *ast.StructDef) !void {
        const alloc = self.compiler.allocator;
        var sigs: std.ArrayList(TypeId) = .empty;
        defer sigs.deinit(alloc);

        for (s.methods.items) |*m| switch (m.*) {
            .func => |*f| {
                try self.check_method_clash(s, f.name, f.token);
                try sigs.append(alloc, try self.declare_func(f, try self.qualify(s.name, f.name)));
            },
            .proc => |*p| {
                try self.check_method_clash(s, p.name, p.token);
                try sigs.append(alloc, try self.declare_proc(p, try self.qualify(s.name, p.name)));
            },
        };
        for (s.methods.items, sigs.items) |*m, sig| switch (m.*) {
            .func => |*f| try self.check_function(f, sig),
            .proc => |*p| try self.check_proc(p, sig),
        };
    }

    fn visit_struct(self: *Sema, s: *ast.StructDef) !void {
        try self.declare_struct(s);
        try self.check_duplicate_fields(s);
        try self.visit_methods(s);
    }

    // `en` / `a`: payloads of the enum_def / alias type_def variants
    fn declare_enum(self: *Sema, en: anytype) !void {
        const alloc = self.compiler.allocator;
        var variants: std.ArrayList(types.EnumVaraintTy) = .empty;
        for (en.variants.items) |*v| {
            for (variants.items) |vt| {
                if (std.mem.eql(u8, vt.name, v.name)) {
                    try self.err("Duplicate variant name: {s}", .{v.name}, v.token);
                }
            }
            var tys: std.ArrayList(TypeId) = .empty;
            for (v.types.items) |t| {
                try tys.append(alloc, try self.resolve_type(t));
            }
            try variants.append(alloc, .{ .name = v.name, .types = tys });
        }

        const ety = try self.types.intern(.{ .enum_ty = .{ .name = en.name, .variants = variants } });
        try self.types.register(en.name, ety);
        try self.declare(.{ .name = en.name, .kind = .@"enum", .ty = ety }, en.token);

        // each variant is also a constructor function: Enum.Variant(payload...) -> Enum
        const edef = self.types.get(ety).enum_ty;
        for (edef.variants.items) |v| {
            const ctorty = try self.types.intern(.{ .function = .{
                .params = try v.types.clone(alloc),
                .result = ety,
            } });
            // duplicate variants were already reported above
            self.scope.declare(.{ .name = try self.qualify(en.name, v.name), .kind = .enum_variant, .ty = ctorty }) catch |e| {
                if (e != error.DuplicateName) return e;
            };
        }
    }

    fn declare_alias(self: *Sema, a: anytype) !void {
        const aty = try self.resolve_type(a.ty);
        if (aty == .invalid) {
            try self.err("cannot resolve aliased type for `{s}`", .{a.name}, a.token);
        }
        try self.types.register(a.name, aty);
        try self.declare(.{ .name = a.name, .kind = .type_alias, .ty = aty }, a.token);
    }

    // --- bodies ---

    // shared by functions and procs: params in a .func scope, body in a nested block
    fn check_fn_body(
        self: *Sema,
        params: anytype,
        param_tys: []const TypeId, // already resolved by declare_*, so no second resolution here
        body: []ast.Stmt,
        info: scope.FnInfo,
    ) !void {
        var fn_scope = scope.Scope.init(self.compiler.allocator, .func, self.scope);
        fn_scope.fn_info = info;
        defer fn_scope.deinit();
        const saved = self.scope;
        self.scope = &fn_scope;
        defer self.scope = saved;

        for (params, param_tys) |*param, pty| {
            const kind: scope.SymbolKind = if (param.is_const) .constant else .variable;
            try self.declare_as("parameter", .{ .name = param.name, .kind = kind, .ty = pty }, param.token);
        }

        try self.enter_scope(body, .block);
    }

    fn check_function(self: *Sema, f: *ast.FunctionDef, fnty: TypeId) !void {
        const sig = self.types.get(fnty).function;
        try self.check_fn_body(f.params.items, sig.params.items, f.body.items, .{ .func = sig.result });

        if (sig.result != .invalid and !stmt_mod.body_returns(f.body.items)) {
            try self.warn("control reaches the end of the function", .{}, f.token);
        }
    }

    fn check_proc(self: *Sema, p: *ast.ProcDef, prty: TypeId) !void {
        const sig = self.types.get(prty).procedure;
        try self.check_fn_body(p.params.items, sig.params.items, p.body.items, .proc);
    }

    // --- ITEMS ---

    // Items are declared and checked one after another, so an
    // item can only use items above it for now.
    fn visit_item(self: *Sema, item: *ast.Item) !void {
        switch (item.*) {
            .import_def => {},
            .function => |*f| {
                const fnty = try self.declare_func(f, f.name);
                try self.check_function(f, fnty);
            },
            .proc => |*p| {
                const prty = try self.declare_proc(p, p.name);
                try self.check_proc(p, prty);
            },
            .type_def => |*t_def| switch (t_def.variant) {
                .struct_def => |*s| try self.visit_struct(s),
                .enum_def => |*en| try self.declare_enum(en),
                .alias => |*a| try self.declare_alias(a),
            },
            .extern_def => |e_def| try self.declare_extern(e_def),
            .var_def => |*v| try self.check_binding(.variable, v.name, v.type_ann, v.value, v.token),
            .const_def => |*c| try self.check_binding(.constant, c.name, c.type_ann, c.value, c.token),
        }
    }
};
