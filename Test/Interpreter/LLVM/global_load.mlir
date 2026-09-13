// RUN: veir-interpret %s | filecheck %s

// Globals are materialized as objects before `main` runs, initialised from
// their `value`, and `llvm.mlir.addressof` yields a pointer to them.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "main"}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %old = "llvm.load"(%g) : (!llvm.ptr) -> i32
    %new = "llvm.add"(%old, %one) : (i32, i32) -> i32
    "llvm.store"(%new, %g) : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%g) : (!llvm.ptr) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32]
