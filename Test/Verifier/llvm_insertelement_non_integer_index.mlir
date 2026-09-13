// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{function_type = (vector<4xi32>, i32, index) -> (), sym_name = "f"}> ({
  ^bb0(%arg0: vector<4xi32>, %arg1: i32, %arg2: index):
    %r = "llvm.insertelement"(%arg0, %arg1, %arg2) : (vector<4xi32>, i32, index) -> vector<4xi32>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.insertelement: Expected operand 2 to have integer type
