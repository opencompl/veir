// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    %c = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %bad = "llvm.mlir.zero"(%c) : (i32) -> !llvm.ptr
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.zero: Expected 0 operand(s)
