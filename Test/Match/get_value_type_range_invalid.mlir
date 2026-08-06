// RUN: not veir-opt %s 2>&1 | filecheck %s

// A range of values gives a range of types, not a single type.
"builtin.module"() ({
  %r = "test.test"() : () -> !pdl.range<value>
  %a = "match.get_value_type"(%r) : (!pdl.range<value>) -> !pdl.type
}) : () -> ()

// CHECK: match.get_value_type: Expected the result to be of type '!pdl.range<type>'
