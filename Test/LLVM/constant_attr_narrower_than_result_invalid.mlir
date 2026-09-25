// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: %if mlir-min-24 %{ MLIR_INVALID %}

// As in MLIR 24, an integer attribute's type must match the result type exactly,
// including an `i1` attribute in a wider result.

"builtin.module"() ({
  "func.func"() <{function_type = () -> i32, sym_name = "f"}> ({
    %c = "llvm.mlir.constant"() <{value = true}> : () -> i32
    "func.return"(%c) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.constant: attribute and type have different integer types: i1 vs. i32
