// RUN: not veir-opt %s 2>&1 | filecheck %s

// The `constantType` property of a `pdl.type` is a type, not an arbitrary
// attribute.
"builtin.module"() ({
  %0 = "pdl.type"() <{"constantType" = "hello"}> : () -> !pdl.type
}) : () -> ()

// CHECK: pdl.type: expected 'constantType' to be a type attribute, but got "hello"
