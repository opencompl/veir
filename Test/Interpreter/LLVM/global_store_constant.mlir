// RUN: veir-interpret %s | filecheck %s

// Storing to a constant global is UB.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, constant, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "main"}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.store"(%one, %g) : (i32, !llvm.ptr) -> ()
    "llvm.return"(%one) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
