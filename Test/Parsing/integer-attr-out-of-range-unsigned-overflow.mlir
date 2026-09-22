// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i8 ()>, linkage = #llvm.linkage<external>, sym_name = "f", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 256 : i8}> : () -> i8
    "llvm.return"(%0) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: error: integer constant out of range for attribute
