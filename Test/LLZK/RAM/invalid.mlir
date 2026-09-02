// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: ram.store: Expected 0 result(s)
"builtin.module"() ({
  "function.def"() <{sym_name = "invalid_ram", function_type = (index, !felt.type) -> ()}> ({
^bb0(%addr: index, %val: !felt.type):
  %0 = "ram.store"(%addr, %val) : (index, !felt.type) -> i32
  "function.return"() : () -> ()
  }) {function.allow_witness} : () -> ()
}) : () -> ()
