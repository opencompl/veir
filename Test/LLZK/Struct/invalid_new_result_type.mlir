// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: struct.new: expected result 0 to have !struct.type
  %0 = "struct.new"() : () -> !felt.type
}) : () -> ()
