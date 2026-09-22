// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i1 ()>, linkage = #llvm.linkage<external>, sym_name = "f", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 2 : i1}> : () -> i1
    "llvm.return"(%0) : (i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute
