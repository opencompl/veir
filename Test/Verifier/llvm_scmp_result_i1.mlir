// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s

// LangRef requires the result to be at least `i2`, to hold -1, 0, and 1.
// `mlir-opt` does not check this, so there is no MLIR cross-check.

"builtin.module"() ({
  %a = "test.value"() : () -> i32
  %b = "test.value"() : () -> i32
  %r = "llvm.intr.scmp"(%a, %b) : (i32, i32) -> i1
}) : () -> ()

// CHECK: llvm.intr.scmp: Expected result type to be at least i2
