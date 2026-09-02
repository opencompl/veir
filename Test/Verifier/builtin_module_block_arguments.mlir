// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: builtin.module: Expected the body block to have 0 arguments
"builtin.module"() ({
^entry(%arg: i1):
}) : () -> ()
