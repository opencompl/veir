// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `!pdl.range` element is one of the four handle types, so ranges never nest.
"builtin.module"() ({
  %0 = "test.test"() : () -> !pdl.range<range<value>>
}) : () -> ()

// CHECK: expected the element of a '!pdl.range' to be one of 'attribute', 'operation', 'type' or 'value'
