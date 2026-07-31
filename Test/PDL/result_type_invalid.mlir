// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `pdl.attribute` produces an `!pdl.attribute` handle, not an `!pdl.type` one.
"builtin.module"() ({
  %0 = "pdl.attribute"() : () -> !pdl.type
}) : () -> ()

// CHECK: pdl.attribute: Expected the result to be of type '!pdl.attribute'
