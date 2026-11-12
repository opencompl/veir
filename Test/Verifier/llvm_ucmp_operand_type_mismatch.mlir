// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s
// RUN: MLIR_UNREGISTERED_INVALID

"builtin.module"() ({
  %a = "test.value"() : () -> i32
  %b = "test.value"() : () -> i16
  %r = "llvm.intr.ucmp"(%a, %b) : (i32, i16) -> i8
}) : () -> ()

// CHECK: llvm.intr.ucmp: Expected operands to have the same type
