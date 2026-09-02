// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: only concrete integer dimensions are supported
"builtin.module"() ({
  "global.def"() <{constant, sym_name = "t", type = !array.type<@N x !felt.type>}> : () -> ()
}) : () -> ()
