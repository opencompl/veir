// RUN: not veir-opt %s 2>&1 | filecheck %s

// `match.extract` yields one element of the range, so the result type is the
// range's element type.
"builtin.module"() ({
  %r = "test.test"() : () -> !pdl.range<value>
  %a = "match.extract"(%r) <{index = 0 : i32}> : (!pdl.range<value>) -> !pdl.type
}) : () -> ()

// CHECK: match.extract: Expected the result to have the element type of the range, '!pdl.value'
