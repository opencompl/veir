// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "global.def"() <{sym_name = "message", constant, type = !string.type, initial_value = "hello"}> : () -> ()
  %0 = "string.new"() <{value = "goodbye"}> : () -> !string.type
  // CHECK: global.write: cannot write to constant global '@message'
  "global.write"(%0) <{name_ref = @message}> : (!string.type) -> ()
}) : () -> ()
