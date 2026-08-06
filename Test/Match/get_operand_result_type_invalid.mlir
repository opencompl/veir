// RUN: not veir-opt %s 2>&1 | filecheck %s

// Navigation that can fail returns `!match.optional<...>`, never a bare handle.
"builtin.module"() ({
  %op = "test.test"() : () -> !pdl.operation
  %a = "match.get_operand"(%op) <{index = 0 : i32}> : (!pdl.operation) -> !pdl.value
}) : () -> ()

// CHECK: match.get_operand: Expected the result to be of type '!match.optional<!pdl.value>'
