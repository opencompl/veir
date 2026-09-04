// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: error: ram.load: expected no properties, but got 1 property
"builtin.module"() ({
^bb0(%addr: index):
  %0 = "ram.load"(%addr) <{unexpected = 1 : i32}> : (index) -> !felt.type
}) : () -> ()
