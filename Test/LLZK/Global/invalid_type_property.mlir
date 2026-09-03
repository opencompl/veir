// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: global.def: expected 'type' to be a type attribute, got "not a type"
  "global.def"() <{sym_name = "bad", type = "not a type"}> : () -> ()
}) : () -> ()
