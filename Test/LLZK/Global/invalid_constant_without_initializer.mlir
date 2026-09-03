// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: global.def: marked as 'constant' must be assigned an initial value
  "global.def"() <{sym_name = "bad", constant, type = !string.type}> : () -> ()
}) : () -> ()
