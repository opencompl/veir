// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  %a = "llvm.mlir.undef"() : () -> i32
  %r = "llvm.intr.sadd.with.overflow"(%a) : (i32) -> !llvm.struct<(i32, i1)>
}) : () -> ()

// CHECK: Expected 2 operand(s)
