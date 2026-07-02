// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

"builtin.module"() ({
^entry:
  "test.test"()[^missing] : () -> ()
}) : () -> ()

// CHECK:forward-reference-missing-block.mlir:5:17: error: block %missing was used but never defined
// CHECK-NEXT:  "test.test"()[^missing] : () -> ()
// CHECK-NEXT:                ^
