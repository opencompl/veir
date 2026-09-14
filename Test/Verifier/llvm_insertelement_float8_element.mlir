// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{function_type = (vector<4xf8E5M2>, f8E5M2, i32) -> (), sym_name = "f"}> ({
  ^bb0(%arg0: vector<4xf8E5M2>, %arg1: f8E5M2, %arg2: i32):
    %r = "llvm.insertelement"(%arg0, %arg1, %arg2) : (vector<4xf8E5M2>, f8E5M2, i32) -> vector<4xf8E5M2>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.insertelement: Expected an LLVM-compatible vector element type, but got f8E5M2
