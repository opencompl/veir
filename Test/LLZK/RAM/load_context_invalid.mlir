// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: Error verifying input program: ram.load: only valid within a 'function.def' with 'function.allow_witness' attribute
"builtin.module"() ({
  "function.def"() <{sym_name = "missing_permission", function_type = (index) -> ()}> ({
  ^bb0(%address: index):
    %0 = "ram.load"(%address) : (index) -> !felt.type
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
