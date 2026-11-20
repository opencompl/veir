// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// An index constant must produce an index value.
"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "main"}> ({
    %0 = "arith.constant"() <{value = 1 : index}> : () -> i64
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected result type to be index
