// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "global.def"() <{sym_name = "message", type = !string.type}> : () -> ()
  // CHECK: global.read: result type does not match '@message'
  %0 = "global.read"() <{name_ref = @message}> : () -> !felt.type
}) : () -> ()
