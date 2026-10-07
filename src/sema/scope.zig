const std = @import("std");
const types = @import("type_system.zig");

pub const SymbolKind = enum {
    variable,
    constant,
    param,
    func,
    proc,
    st_field,
    @"struct",
    type_alias,
    @"enum",
    enum_variant,
};

pub const FnInfo = union(enum) {
    func: types.TypeId, // returns value so typeid
    proc, // should never return a value, tho it could return from branches
};

pub const Symbol = struct {
    name: []const u8,
    kind: SymbolKind,
    ty: types.TypeId = .invalid,
    has_self: bool = false, // self as first param (for struct)
    const_val: ?u64 = null,
    // here we keep growing accordingly,
};

pub const Scope = struct {
    id: Id,
    parent: ?*Scope,
    symbols: std.StringHashMap(Symbol), // for O(1)
    fn_info: ?FnInfo = null, // this used only for .func SymbolKind scopes

    pub const Id = enum {
        root, // root (var_def, const_def)
        block, // if, elif, else, etc...
        func, // both func and proc
        loop,
        unsafe,
        @"struct",
    };

    pub fn init(allocator: std.mem.Allocator, id: Id, parent: ?*Scope) Scope {
        return .{
            .id = id,
            .parent = parent,
            .symbols = std.StringHashMap(Symbol).init(allocator),
        };
    }

    pub fn deinit(self: *Scope) void {
        self.symbols.deinit();
    }

    // rule of duplication
    pub fn declare(self: *Scope, symbol: Symbol) !void {
        if (self.symbols.contains(symbol.name)) return error.DuplicateName;
        try self.symbols.put(symbol.name, symbol);
    }

    // resolve name keep going outward towards upper scope
    pub fn resolve(self: *Scope, name: []const u8) ?Symbol {
        var cur: ?*Scope = self;
        while (cur) |s| {
            if (s.symbols.get(name)) |sym| return sym;
            cur = s.parent;
        }
        return null;
    }

    // search outward for a given scope id
    pub fn enclosing(self: *Scope, id: Id) ?*Scope {
        var cur: ?*Scope = self;
        while (cur) |s| {
            if (s.id == id) return s;
            cur = s.parent;
        }
        return null;
    }
};
