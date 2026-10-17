const std = @import("std");
const ast = @import("../ast.zig");

pub const TypeId = enum(u32) {
    invalid = 0,
    _,
};

// `.invalid` means "nothing known"; as an expected-type hint that is `null`.
pub fn hint(id: TypeId) ?TypeId {
    return if (id != .invalid) id else null;
}

pub const Primitive = enum {
    // zig fmt: off
    bool, char, str,
    i8, i16, i32, i64,
    u8, u16, u32, u64,
    f32, f64,
    usize, isize,
    ptr,
    // zig fmt: on
};

pub const StFieldTy = struct { name: []const u8, ty: TypeId }; // struct field ka type
pub const EnumVaraintTy = struct { name: []const u8, types: std.ArrayList(TypeId) }; // enum variant ka type

pub const Type = union(enum) {
    primitive: Primitive,
    pointer: struct { child: TypeId },
    array: struct { child: TypeId, len: u64 },
    slice: struct { child: TypeId },
    optional: TypeId,
    error_union: TypeId,
    function: struct { params: std.ArrayList(TypeId), result: TypeId, is_variadic: bool = false },
    procedure: struct { params: std.ArrayList(TypeId), is_variadic: bool = false },
    range: struct { elem: TypeId },
    struct_ty: struct { name: []const u8, fields: std.ArrayList(StFieldTy) },
    enum_ty: struct { name: []const u8, variants: std.ArrayList(EnumVaraintTy) },
};

// this struct owns every type. Types are interned (structurally equal types share one
// `TypeId`), so type equality everywhere else is just `a == b`.
pub const TypeSystem = struct {
    allocator: std.mem.Allocator,
    types: std.ArrayList(Type),
    arena: std.heap.ArenaAllocator,
    pids: [@typeInfo(Primitive).@"enum".field_names.len]TypeId, // primtive ids
    struct_reg: std.StringArrayHashMapUnmanaged(TypeId) = .empty, // struct registry for storing all defined struct (for codegen)

    heads: std.AutoHashMapUnmanaged(u64, TypeId) = .{},
    next_same_hash: std.ArrayList(TypeId) = .empty,

    pub fn init(allocator: std.mem.Allocator) TypeSystem {
        return .{
            .allocator = allocator,
            .types = .empty,
            .pids = @splat(.invalid),
            .arena = std.heap.ArenaAllocator.init(allocator),
        };
    }

    pub fn deinit(self: *TypeSystem) void {
        for (self.types.items) |*ty| release(self.allocator, ty);
        self.types.deinit(self.allocator);
        self.next_same_hash.deinit(self.allocator);
        self.heads.deinit(self.allocator);
        self.arena.deinit();
        self.struct_reg.deinit(self.allocator);
    }

    // frees the heap lists a Type owns
    fn release(allocator: std.mem.Allocator, ty: *Type) void {
        switch (ty.*) {
            .function => |*f| f.params.deinit(allocator),
            .procedure => |*p| p.params.deinit(allocator),
            .struct_ty => |*s| s.fields.deinit(allocator),
            .enum_ty => |*e| {
                for (e.variants.items) |*v| v.types.deinit(allocator);
                e.variants.deinit(allocator);
            },
            else => {},
        }
    }

    pub fn get(self: *TypeSystem, id: TypeId) *Type {
        std.debug.assert(id != .invalid);
        return &self.types.items[@backingInt(id) - 1];
    }

    // append a type without looking for an equal one (prefer `intern`)
    pub fn add(self: *TypeSystem, ty: Type) !TypeId {
        return self.add_hashed(ty, hash_type(ty));
    }

    fn add_hashed(self: *TypeSystem, ty: Type, h: u64) !TypeId {
        // reserve everything first so a failure can't leave the index half updated
        try self.types.ensureUnusedCapacity(self.allocator, 1);
        try self.next_same_hash.ensureUnusedCapacity(self.allocator, 1);
        const slot = try self.heads.getOrPut(self.allocator, h);

        self.types.appendAssumeCapacity(ty);
        const id: TypeId = @fromBackingInt(@intCast(self.types.items.len));
        self.next_same_hash.appendAssumeCapacity(if (slot.found_existing) slot.value_ptr.* else .invalid);
        slot.value_ptr.* = id;
        return id;
    }

    fn find(self: *TypeSystem, ty: Type, h: u64) ?TypeId {
        var cur = self.heads.get(h) orelse return null;
        while (cur != .invalid) : (cur = self.next_same_hash.items[@backingInt(cur) - 1]) {
            if (is_type_eql(self.get(cur).*, ty)) return cur;
        }
        return null;
    }

    // returns the canonical id for `ty`, adding it if it is new.
    // takes ownership of any lists inside `ty` (freed if an equal type exists).
    pub fn intern(self: *TypeSystem, ty: Type) !TypeId {
        const h = hash_type(ty);
        if (self.find(ty, h)) |id| {
            var discarded = ty;
            release(self.allocator, &discarded);
            return id;
        }
        return self.add_hashed(ty, h);
    }

    pub fn primitive(self: *TypeSystem, p: Primitive) !TypeId {
        const idx = @backingInt(p);
        if (self.pids[idx] != .invalid) {
            return self.pids[idx];
        }
        const id = try self.add(.{ .primitive = p });
        self.pids[idx] = id;
        return id;
    }

    fn hash_id(h: *std.hash.Wyhash, id: TypeId) void {
        const v: u32 = @backingInt(id);
        h.update(std.mem.asBytes(&v));
    }

    fn hash_type(ty: Type) u64 {
        var h = std.hash.Wyhash.init(0);
        const tag: u32 = @backingInt(std.meta.activeTag(ty));
        h.update(std.mem.asBytes(&tag));
        switch (ty) {
            .primitive => |p| {
                const v: u32 = @backingInt(p);
                h.update(std.mem.asBytes(&v));
            },
            .pointer => |p| hash_id(&h, p.child),
            .array => |a| {
                hash_id(&h, a.child);
                h.update(std.mem.asBytes(&a.len));
            },
            .slice => |s| hash_id(&h, s.child),
            .optional => |c| hash_id(&h, c),
            .error_union => |c| hash_id(&h, c),
            .function => |f| {
                h.update(std.mem.sliceAsBytes(f.params.items));
                hash_id(&h, f.result);
                const variadic: u8 = if (f.is_variadic) 1 else 0;
                h.update(std.mem.asBytes(&variadic));
            },
            .procedure => |p| {
                h.update(std.mem.sliceAsBytes(p.params.items));
                const variadic: u8 = if (p.is_variadic) 1 else 0;
                h.update(std.mem.asBytes(&variadic));
            },
            .range => |r| hash_id(&h, r.elem),
            .struct_ty => |s| h.update(s.name),
            .enum_ty => |e| h.update(e.name),
        }
        return h.final();
    }

    fn is_type_eql(a: Type, b: Type) bool {
        if (@as(std.meta.Tag(Type), a) != @as(std.meta.Tag(Type), b)) return false;
        return switch (a) {
            .primitive => a.primitive == b.primitive,
            .pointer => a.pointer.child == b.pointer.child,
            .array => a.array.child == b.array.child and a.array.len == b.array.len,
            .slice => a.slice.child == b.slice.child,
            .optional => a.optional == b.optional,
            .error_union => a.error_union == b.error_union,
            .function => (a.function.result == b.function.result) and
                (a.function.is_variadic == b.function.is_variadic) and
                std.mem.eql(TypeId, a.function.params.items, b.function.params.items),
            .procedure => (a.procedure.is_variadic == b.procedure.is_variadic) and
                std.mem.eql(TypeId, a.procedure.params.items, b.procedure.params.items),
            .range => a.range.elem == b.range.elem,
            .struct_ty => std.mem.eql(u8, a.struct_ty.name, b.struct_ty.name),
            .enum_ty => std.mem.eql(u8, a.enum_ty.name, b.enum_ty.name),
        };
    }

    // for mapping ast primitive to sema primitive
    pub fn from_ast_primitive(self: *TypeSystem, p: ast.PrimitiveType) !TypeId {
        const mapped = std.meta.stringToEnum(Primitive, @tagName(p)) orelse unreachable;
        return self.primitive(mapped);
    }

    // -------- numeric classification ------ //

    const NumKind = enum { signed, unsigned, float };
    const NumRank = struct { kind: NumKind, bits: u8 };

    // the numrank is rank of types in our bedrock
    // according to their signededness and no. of bits
    fn numeric_rank(p: Primitive) ?NumRank {
        return switch (p) {
            .i8 => .{ .kind = .signed, .bits = 8 },
            .i16 => .{ .kind = .signed, .bits = 16 },
            .i32 => .{ .kind = .signed, .bits = 32 },
            .i64, .isize => .{ .kind = .signed, .bits = 64 },
            .u8 => .{ .kind = .unsigned, .bits = 8 },
            .u16 => .{ .kind = .unsigned, .bits = 16 },
            .u32 => .{ .kind = .unsigned, .bits = 32 },
            .u64, .usize => .{ .kind = .unsigned, .bits = 64 },
            .f32 => .{ .kind = .float, .bits = 32 },
            .f64 => .{ .kind = .float, .bits = 64 },
            .bool, .char, .str, .ptr => null,
        };
    }

    fn rank_of(self: *TypeSystem, id: TypeId) ?NumRank {
        if (id == .invalid) return null;
        return switch (self.get(id).*) {
            .primitive => |p| numeric_rank(p),
            else => null,
        };
    }

    // integers and floats
    pub fn is_numeric(self: *TypeSystem, id: TypeId) bool {
        return self.rank_of(id) != null;
    }

    pub fn is_integer(self: *TypeSystem, id: TypeId) bool {
        const r = self.rank_of(id) orelse return false;
        return r.kind != .float;
    }

    pub fn is_unsigned(self: *TypeSystem, id: TypeId) bool {
        const r = self.rank_of(id) orelse return false;
        return r.kind == .unsigned;
    }

    // ------ conversions ----- //

    // when conversion situation arise we will use to find out
    // if we can implicitly convert between two types (from -> to)
    pub fn can_implicit_convert(from: Primitive, to: Primitive) bool {
        if (from == to) return true;
        const f = numeric_rank(from) orelse return false;
        const t = numeric_rank(to) orelse return false;
        if (f.kind != t.kind) return t.kind == .float and f.kind != .float;
        // i8 -> i16 (common sense)
        // or i64 -> isize and u64 -> usize (same)
        return t.bits >= f.bits;
    }

    // to check if an id (from) can be assign to another id (to)
    // it's useful for type conversion checking.
    pub fn assignable(self: *TypeSystem, from: TypeId, to: TypeId) bool {
        if (from == .invalid or to == .invalid) return true;
        if (from == to) return true;
        return switch (self.get(to).*) {
            .primitive => |pto| switch (self.get(from).*) {
                .primitive => |pfrom| can_implicit_convert(pfrom, pto),
                else => false,
            },
            .optional => |inner| from == inner or self.assignable(from, inner),
            .error_union => |inner| from == inner or self.assignable(from, inner),
            .slice => |s| switch (self.get(from).*) {
                .array => |a| self.assignable(a.child, s.child),
                else => false,
            },
            else => false,
        };
    }

    pub fn unify(self: *TypeSystem, a: TypeId, b: TypeId) ?TypeId {
        if (a == .invalid) return b;
        if (b == .invalid or a == b) return a;
        if (self.assignable(a, b)) return b;
        if (self.assignable(b, a)) return a;
        return null;
    }

    // find type of literal "hi" -> string, 24 -> i32
    pub fn literal_type(self: *TypeSystem, kind: ast.LiteralKind) !TypeId {
        return switch (kind) {
            .integer => self.primitive(.i32),
            .float => self.primitive(.f64),
            .string => self.primitive(.str),
            .char => self.primitive(.char),
            .bool_true, .bool_false => self.primitive(.bool),
        };
    }

    // does literal fits this type
    pub fn literal_fits(self: *TypeSystem, kind: ast.LiteralKind, id: TypeId) bool {
        if (id == .invalid) return false;
        const p = switch (self.get(id).*) {
            .primitive => |p| p,
            else => return false,
        };
        return switch (kind) {
            .integer => switch (p) {
                .i8, .i16, .i32, .i64, .u8, .u16, .u32, .u64, .f32, .f64, .usize, .isize => true,
                else => false,
            },
            .float => switch (p) {
                .f32, .f64 => true,
                else => false,
            },
            else => false,
        };
    }

    pub fn name_of(self: *TypeSystem, id: TypeId) []const u8 {
        if (id == .invalid) return "<invalid>";
        return switch (self.get(id).*) {
            .primitive => |p| @tagName(p),
            .array => |a| std.fmt.allocPrint(self.arena.allocator(), "[{d}]{s}", .{ a.len, self.name_of(a.child) }) catch "<oom>",
            .slice => |s| std.fmt.allocPrint(self.arena.allocator(), "[]{s}", .{self.name_of(s.child)}) catch "<oom>",
            .struct_ty => |*s| s.name,
            .enum_ty => |*e| e.name,
            else => "not implemented",
        };
    }

    // it gets the struct type of a pointer struct
    // and a normal struct so (self: *P) and (self: P)
    // could be called in same way (p.foo()) and not (&p.foo())
    pub fn struct_of(self: *TypeSystem, tty: TypeId) TypeId {
        if (tty == .invalid) return .invalid;
        return switch (self.get(tty).*) {
            .struct_ty, .enum_ty => tty,
            .pointer => |p| if (p.child != .invalid and self.get(p.child).* == .struct_ty) p.child else .invalid,
            else => .invalid,
        };
    }

    // struct or named type specific things //
    pub fn register(self: *TypeSystem, name: []const u8, id: TypeId) !void {
        try self.struct_reg.put(self.allocator, name, id);
    }

    pub fn resolve(self: *TypeSystem, name: []const u8) ?TypeId {
        return self.struct_reg.get(name);
    }
};
