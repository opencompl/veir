// RUN: VEIR_UNREGISTERED_ROUNDTRIP
// RUN: MLIR_UNREGISTERED_ROUNDTRIP

// Every integer attribute is normalized to its width when parsed, not just the
// `value` of a constant: MLIR does this in the attribute parser itself, so it
// applies to discardable attributes and to any dialect's properties alike.

"builtin.module"() ({
  "test.op"() {a = 200 : i8} : () -> ()
  "test.op"() {a = 0x80 : i8} : () -> ()
  "test.op"() {a = 3 : i2} : () -> ()
  "test.op"() {a = -1 : i1} : () -> ()
  "test.op"() {a = 18446744073709551615 : i64} : () -> ()
  // Already normalized: must round-trip unchanged.
  "test.op"() {a = -128 : i8} : () -> ()
  "test.op"() {a = 127 : i8} : () -> ()
  %0 = "hw.constant"() <{value = 200 : i8}> : () -> i8
  %1 = "arith.constant"() <{value = 7 : i8}> {tag = 255 : i8} : () -> i8
}) : () -> ()

// CHECK:      "test.op"() {"a" = -56 : i8} : () -> ()
// CHECK-NEXT: "test.op"() {"a" = -128 : i8} : () -> ()
// CHECK-NEXT: "test.op"() {"a" = -1 : i2} : () -> ()
// CHECK-NEXT: "test.op"() {"a" = true} : () -> ()
// CHECK-NEXT: "test.op"() {"a" = -1 : i64} : () -> ()
// CHECK-NEXT: "test.op"() {"a" = -128 : i8} : () -> ()
// CHECK-NEXT: "test.op"() {"a" = 127 : i8} : () -> ()
// CHECK-NEXT: "hw.constant"() <{"value" = -56 : i8}> : () -> i8
// CHECK-NEXT: "arith.constant"() <{"value" = 7 : i8}> {"tag" = -1 : i8} : () -> i8
