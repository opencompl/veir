// RUN: not veir-opt %s 2>&1 | filecheck %s

// CHECK: function.def: expected a supported LLZK type, got i32
"builtin.module"() ({
  "function.def"() <{sym_name = "bad", function_type = (i32) -> ()}> ({
  ^entry(%x : i32):
    "function.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
