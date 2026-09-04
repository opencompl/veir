// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: global.def: initial value #felt<const 1> is incompatible with type !string.type
  "global.def"() <{sym_name = "bad", type = !string.type, initial_value = #felt<const 1> : !felt.type}> : () -> ()
}) : () -> ()
