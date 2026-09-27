// RUN: not veir-opt %s --allow-unregistered-dialect 2>&1 | filecheck %s

"builtin.module"() ({
  "test.op"() : () -> s32
}) : () -> ()

// CHECK: error
