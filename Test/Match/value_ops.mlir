// RUN: VEIR_ROUNDTRIP

// `MLIR_ROUNDTRIP` is deliberately absent: `match` is an unmerged upstream
// proposal, so no released `mlir-opt` knows these operations. Add it once it
// lands.
//
// The value-producing subset of the dialect: constants and navigation, all of
// them `Pure`. Navigation that can fail returns `!match.optional<...>`; the
// rest return bare handles.

"builtin.module"() ({
  %op = "test.test"() : () -> !pdl.operation
  %val = "test.test"() : () -> !pdl.value
  %vals = "test.test"() : () -> !pdl.range<value>
  %attr = "test.test"() : () -> !pdl.attribute

  %ca = "match.constant_attribute"() <{value = 42 : i32}> : () -> !pdl.attribute
  %ct = "match.constant_type"() <{value = i32}> : () -> !pdl.type
  %cts = "match.constant_types"() <{value = [i32, i64]}> : () -> !pdl.range<type>

  // Nullable navigation. `get_operands` and `get_results` take an optional
  // index; without one they stand for the whole list.
  %o0 = "match.get_operand"(%op) <{index = 0 : i32}> : (!pdl.operation) -> !match.optional<!pdl.value>
  %os = "match.get_operands"(%op) : (!pdl.operation) -> !match.optional<!pdl.range<value>>
  %r0 = "match.get_result"(%op) <{index = 0 : i32}> : (!pdl.operation) -> !match.optional<!pdl.value>
  %rs = "match.get_results"(%op) <{index = 1 : i32}> : (!pdl.operation) -> !match.optional<!pdl.range<value>>
  %ga = "match.get_attribute"(%op) <{name = "value"}> : (!pdl.operation) -> !match.optional<!pdl.attribute>
  %def = "match.get_defining_op"(%val) : (!pdl.value) -> !match.optional<!pdl.operation>

  // Non-nullable navigation. A range in gives a range out.
  %vt = "match.get_value_type"(%val) : (!pdl.value) -> !pdl.type
  %vts = "match.get_value_type"(%vals) : (!pdl.range<value>) -> !pdl.range<type>
  %at = "match.get_attribute_type"(%attr) : (!pdl.attribute) -> !pdl.type
  %us = "match.get_users"(%val) : (!pdl.value) -> !pdl.range<operation>
  %ex = "match.extract"(%vals) <{index = 0 : i32}> : (!pdl.range<value>) -> !pdl.value
  %ea = "match.get_each"(%vals) : (!pdl.range<value>) -> !pdl.value
}) : () -> ()

// CHECK:      %[[op:.*]] = "test.test"() : () -> !pdl.operation
// CHECK-NEXT: %[[val:.*]] = "test.test"() : () -> !pdl.value
// CHECK-NEXT: %[[vals:.*]] = "test.test"() : () -> !pdl.range<value>
// CHECK-NEXT: %[[attr:.*]] = "test.test"() : () -> !pdl.attribute
// CHECK-NEXT: %{{.*}} = "match.constant_attribute"() <{"value" = 42 : i32}> : () -> !pdl.attribute
// CHECK-NEXT: %{{.*}} = "match.constant_type"() <{"value" = i32}> : () -> !pdl.type
// CHECK-NEXT: %{{.*}} = "match.constant_types"() <{"value" = [i32, i64]}> : () -> !pdl.range<type>
// CHECK-NEXT: %{{.*}} = "match.get_operand"(%[[op]]) <{"index" = 0 : i32}> : (!pdl.operation) -> !match.optional<!pdl.value>
// CHECK-NEXT: %{{.*}} = "match.get_operands"(%[[op]]) : (!pdl.operation) -> !match.optional<!pdl.range<value>>
// CHECK-NEXT: %{{.*}} = "match.get_result"(%[[op]]) <{"index" = 0 : i32}> : (!pdl.operation) -> !match.optional<!pdl.value>
// CHECK-NEXT: %{{.*}} = "match.get_results"(%[[op]]) <{"index" = 1 : i32}> : (!pdl.operation) -> !match.optional<!pdl.range<value>>
// CHECK-NEXT: %{{.*}} = "match.get_attribute"(%[[op]]) <{"name" = "value"}> : (!pdl.operation) -> !match.optional<!pdl.attribute>
// CHECK-NEXT: %{{.*}} = "match.get_defining_op"(%[[val]]) : (!pdl.value) -> !match.optional<!pdl.operation>
// CHECK-NEXT: %{{.*}} = "match.get_value_type"(%[[val]]) : (!pdl.value) -> !pdl.type
// CHECK-NEXT: %{{.*}} = "match.get_value_type"(%[[vals]]) : (!pdl.range<value>) -> !pdl.range<type>
// CHECK-NEXT: %{{.*}} = "match.get_attribute_type"(%[[attr]]) : (!pdl.attribute) -> !pdl.type
// CHECK-NEXT: %{{.*}} = "match.get_users"(%[[val]]) : (!pdl.value) -> !pdl.range<operation>
// CHECK-NEXT: %{{.*}} = "match.extract"(%[[vals]]) <{"index" = 0 : i32}> : (!pdl.range<value>) -> !pdl.value
// CHECK-NEXT: %{{.*}} = "match.get_each"(%[[vals]]) : (!pdl.range<value>) -> !pdl.value
