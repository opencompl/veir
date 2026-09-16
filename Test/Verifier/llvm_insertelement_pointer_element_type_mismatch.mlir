// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "func.func"() <{function_type = (vector<4x!llvm.ptr>, i64, i32) -> (), sym_name = "f"}> ({
  ^bb0(%arg0: vector<4x!llvm.ptr>, %arg1: i64, %arg2: i32):
    %r = "llvm.insertelement"(%arg0, %arg1, %arg2) : (vector<4x!llvm.ptr>, i64, i32) -> vector<4x!llvm.ptr>
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.insertelement: Expected operand 1 to have vector element type !llvm.ptr, but got i64
