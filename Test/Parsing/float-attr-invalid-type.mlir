// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that a float attribute with an unsupported type suffix is rejected.

"builtin.module"() ({
  "test.test"() {"v" = 1.5 : f245} : () -> ()
}) : () -> ()

// CHECK:float-attr-invalid-type.mlir:6:30: error: integer or float type expected after ':' in numeric attribute
// CHECK-NEXT:  "test.test"() {"v" = 1.5 : f245} : () -> ()
// CHECK-NEXT:                             ^
