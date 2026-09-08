// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that a decimal integer literal is rejected for a float type: only a
// 0x-prefixed hexadecimal bit pattern or a decimal floating-point literal is
// allowed as the value of a float attribute.

"builtin.module"() ({
  "test.test"() {"v" = 10 : f32} : () -> ()
}) : () -> ()

// CHECK:float-attr-invalid-value.mlir:8:24: error: expected a decimal float or 0x-prefixed hex bit pattern in float attribute
// CHECK-NEXT:  "test.test"() {"v" = 10 : f32} : () -> ()
// CHECK-NEXT:                        ^
