// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

"builtin.module"() ({
  %a = "test.value"() : () -> i32
  %b = "test.value"() : () -> i32
  %r = "llvm.intr.umul.with.overflow"(%a, %b) : (i32, i32) -> index
}) : () -> ()

// CHECK: result #0 must be !llvm.struct<(i32, i1)>
