// RUN: not veir-opt %s 2>&1 | filecheck %s

// A `pdl.type` produces an `!pdl.type` handle, not the type it is constrained to.
"builtin.module"() ({
  %0 = "pdl.type"() <{"constantType" = i32}> : () -> i32
}) : () -> ()

// CHECK: pdl.type: Expected the result to be of type '!pdl.type'
