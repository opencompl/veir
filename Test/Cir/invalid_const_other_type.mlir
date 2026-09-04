// RUN: not veir-opt --allow-unregistered-dialect %s 2>&1 | filecheck %s

// An unmodelled constant value still has to agree with the result type when it carries one.
// CHECK: cir.const: Expected result type to match the constant's type
"builtin.module"() ({
  %0 = "cir.const"() <{value = #cir.ptr<null> : !cir.ptr<!cir.int<s, 32>>}> : () -> !cir.int<s, 32>
}) : () -> ()
