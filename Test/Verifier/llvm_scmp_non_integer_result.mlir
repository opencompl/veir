// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

"builtin.module"() ({
  %a = "test.value"() : () -> i32
  %b = "test.value"() : () -> i32
  %r = "llvm.intr.scmp"(%a, %b) : (i32, i32) -> f32
}) : () -> ()

// CHECK: llvm.intr.scmp: Expected integer result type
