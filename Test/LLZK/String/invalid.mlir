// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: string.new: Expected 1 result(s)
"builtin.module"() ({
^bb0():
  %0:2 = "string.new"() <{value = "hello"}> : () -> (!string.type, !string.type)
}) : () -> ()
