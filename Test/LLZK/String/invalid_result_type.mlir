// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: string.new: expected result 0 to have !string.type
  %0 = "string.new"() <{value = "hello"}> : () -> i32
}) : () -> ()
