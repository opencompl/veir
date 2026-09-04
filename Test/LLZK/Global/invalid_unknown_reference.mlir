// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  // CHECK: global.read: '@missing' does not name a global.def
  %0 = "global.read"() <{name_ref = @missing}> : () -> !string.type
}) : () -> ()
