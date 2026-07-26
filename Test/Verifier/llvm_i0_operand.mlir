// RUN: not veir-opt %s 2>&1 | filecheck %s

// An `llvm` operation may not accept an `i0` value.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = (i0) -> ()}> ({
  ^bb0(%arg0: i0):
    %x = "llvm.zext"(%arg0) : (i0) -> i8
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.zext: operand 0 has forbidden i0 type
