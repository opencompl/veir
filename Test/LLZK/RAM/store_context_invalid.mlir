// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: ram.store: only valid within a 'function.def' with 'function.allow_witness' attribute
"builtin.module"() ({
  "function.def"() <{sym_name = "missing_permission", function_type = (index, !felt.type) -> ()}> ({
  ^bb0(%address: index, %value: !felt.type):
    "ram.store"(%address, %value) : (index, !felt.type) -> ()
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
