// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: missing 'name_ref' property
"builtin.module"() ({
  %0 = "global.read"() : () -> i32
}) : () -> ()
