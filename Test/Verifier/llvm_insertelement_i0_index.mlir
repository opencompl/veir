// RUN: not veir-opt %s 2>&1 | filecheck %s

// VeIR's LLVM dialect rejects i0, although MLIR accepts it.

"builtin.module"() ({
  "func.func"() <{function_type = (vector<4xi32>, i32, i0) -> (), sym_name = "f"}> ({
  ^bb0(%arg0: vector<4xi32>, %arg1: i32, %arg2: i0):
    %r = "llvm.insertelement"(%arg0, %arg1, %arg2) : (vector<4xi32>, i32, i0) -> vector<4xi32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.insertelement: operand 2 has forbidden i0 type
