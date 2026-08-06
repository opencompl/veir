// RUN: not veir-opt %s 2>&1 | filecheck %s

// The index of `match.get_operand` is mandatory and non-negative.
"builtin.module"() ({
  %op = "test.test"() : () -> !pdl.operation
  %a = "match.get_operand"(%op) <{index = -1 : i32}> : (!pdl.operation) -> !match.optional<!pdl.value>
}) : () -> ()

// CHECK: match.get_operand: expected 'index' to be non-negative, but got -1
