// RUN: not veir-opt %s 2>&1 | filecheck %s

// An `llvm` operation may not produce an `i0` value.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i8) -> ()}> ({
  ^bb0(%arg0: i8):
    %x = "llvm.trunc"(%arg0) : (i8) -> i0
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.trunc: result 0 has forbidden i0 type
