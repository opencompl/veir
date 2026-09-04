// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: Error verifying input program: include.from: Expected 0 result(s)
  %0 = "include.from"() <{sym_name = "lib_a", path = "lib_a.llzk"}> : () -> (i32)
}) : () -> ()
