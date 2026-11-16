// RUN: veir-interpret %s | filecheck %s

// A load through `g_global_value` reads the global's `value`.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 1 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "main"}> ({
    %g = "gmir.g_global_value"() <{global_name = @g}> : () -> !llvm.ptr
    %r = "gmir.g_load"(%g) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
