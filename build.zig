const std = @import("std");

pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});

    const translate_llvm = b.addTranslateC(.{
        .root_source_file = b.path("src/llvm.h"),
        .target = target,
        .optimize = optimize,
    });

    const llvm_prefix = b.run(&.{ "llvm-config", "--prefix" });
    const llvm_include = b.fmt("{s}/include", .{std.mem.trim(u8, llvm_prefix, "\n")});
    translate_llvm.addIncludePath(.{
        .cwd_relative = llvm_include,
    });

    const exe = b.addExecutable(.{
        .name = "bok",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
            .imports = &.{
                .{
                    .name = "llvm",
                    .module = translate_llvm.createModule(),
                },
            },
        }),
    });

    b.installArtifact(exe);
    const run_step = b.step("run", "Run the app");
    const run_cmd = b.addRunArtifact(exe);
    run_step.dependOn(&run_cmd.step);
    run_cmd.step.dependOn(b.getInstallStep());

    run_cmd.addPassthruArgs();

    exe.root_module.linkSystemLibrary("LLVM", .{});
    const exe_tests = b.addTest(.{
        .root_module = exe.root_module,
    });

    const memory = b.addLibrary(.{
        .name = "memory",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/memory/memory.zig"),
            .target = target,
            .optimize = optimize,
        }),
        .linkage = .dynamic,
    });

    b.installArtifact(memory);

    const run_exe_tests = b.addRunArtifact(exe_tests);
    const test_step = b.step("test", "Run tests");
    test_step.dependOn(&run_exe_tests.step);

    const bedrock_mod = b.addModule("bedrock", .{
        .root_source_file = b.path("src/root.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
        .imports = &.{
            .{ .name = "llvm", .module = translate_llvm.createModule() },
        },
    });

    const test_root = b.createModule(.{
        .root_source_file = b.path("tests/root.zig"),
        .target = target,
        .optimize = optimize,
        .link_libc = true,
        .imports = &.{
            .{ .name = "bedrock", .module = bedrock_mod },
        },
    });

    test_root.linkSystemLibrary("LLVM", .{});
    const all_tests = b.addTest(.{
        .root_module = test_root,
    });

    test_step.dependOn(&b.addRunArtifact(all_tests).step);
}
