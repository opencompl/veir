// RUN: veir-opt %s | filecheck %s

// A `builtin.module` does not require a terminator

"builtin.module"() ({
^bb0():
}) : () -> ()

// CHECK: "builtin.module"() ({
