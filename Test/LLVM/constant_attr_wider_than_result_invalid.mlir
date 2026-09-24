// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// As in MLIR, an integer attribute's type must match the result type exactly.

"builtin.module"() ({
  "func.func"() <{function_type = () -> i8, sym_name = "f"}> ({
    %c = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i8
    "func.return"(%c) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.constant: attribute and type have different integer types: i32 vs. i8
