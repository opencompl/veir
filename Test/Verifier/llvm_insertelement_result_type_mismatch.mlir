// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{function_type = (vector<4xi32>, i32, i32) -> (), sym_name = "f"}> ({
  ^bb0(%arg0: vector<4xi32>, %arg1: i32, %arg2: i32):
    %r = "llvm.insertelement"(%arg0, %arg1, %arg2) : (vector<4xi32>, i32, i32) -> vector<2xi32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.insertelement: Expected the result to have the vector type
