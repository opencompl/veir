// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "struct.def"() <{sym_name = "Bad"}> ({
    // CHECK: struct.member: expected 'type' to be a supported LLZK type
    "struct.member"() <{sym_name = "field", type = f32}> : () -> ()
  }) : () -> ()
}) : () -> ()
