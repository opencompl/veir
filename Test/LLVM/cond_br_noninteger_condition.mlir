// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A condition that is not an integer at all, which `checkIsNonNullIntegerType`
// lets through since it only constrains the integer operands.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i64 (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    "llvm.cond_br"(%p) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (!llvm.ptr) -> ()
  ^bb1():
    %t = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    "llvm.return"(%t) : (i64) -> ()
  ^bb2():
    %f = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    "llvm.return"(%f) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.cond_br: 'llvm.cond_br' op operand #0 must be of type i1
