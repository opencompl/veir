// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: missing 'sym_name' property
"builtin.module"() ({
  "struct.def"() <{sym_name = "Bad"}> ({
    "struct.member"() <{type = !felt.type}> : () -> ()
  }) : () -> ()
}) : () -> ()
