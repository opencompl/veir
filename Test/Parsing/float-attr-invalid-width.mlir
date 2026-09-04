// RUN: not veir-opt %s 2>&1 | filecheck %s --strict-whitespace

// Verify that a 0x-prefixed bit pattern wider than the float type is rejected
// rather than silently truncated to the low bits of the type.

"builtin.module"() ({
  "test.test"() {"v" = 0xdeadbeefdeadbeef : f32} : () -> ()
}) : () -> ()

// CHECK: hexadecimal float constant out of range for type
