// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

"builtin.module"() ({
  %a = "test.value"() : () -> f32
  %b = "test.value"() : () -> f32
  %r = "llvm.intr.sadd.with.overflow"(%a, %b) : (f32, f32) -> i32
}) : () -> ()

// CHECK: operand #0 must be a signless integer
