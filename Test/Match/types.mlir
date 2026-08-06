// RUN: VEIR_ROUNDTRIP

// `MLIR_ROUNDTRIP` is deliberately absent: the `match` dialect is an unmerged
// upstream proposal, so no released `mlir-opt` knows `!match.optional`. Add the
// round-trip once it lands.

"builtin.module"() ({
  %0 = "test.test"() : () -> !match.optional<!pdl.operation>
  %1 = "test.test"() : () -> !match.optional<!pdl.value>
  %2 = "test.test"() : () -> !match.optional<!pdl.attribute>
  %3 = "test.test"() : () -> !match.optional<!pdl.type>
  // The wrapped type is parsed with the general type parser, so a range and
  // even a non-PDL type round-trip. MLIR narrows this in the type verifier,
  // which is not modelled yet.
  %4 = "test.test"() : () -> !match.optional<!pdl.range<value>>
  %5 = "test.test"() : () -> !match.optional<i32>
}) : () -> ()

// CHECK:      "builtin.module"() ({
// CHECK-NEXT:   ^{{.*}}():
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !match.optional<!pdl.operation>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !match.optional<!pdl.value>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !match.optional<!pdl.attribute>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !match.optional<!pdl.type>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !match.optional<!pdl.range<value>>
// CHECK-NEXT:     %{{.*}} = "test.test"() : () -> !match.optional<i32>
// CHECK-NEXT: }) : () -> ()
