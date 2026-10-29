// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "bad", function_type = (i32, i32) -> i32}> ({
  ^bb(%a: i32, %b: i32):
    %r = "gmir.g_addw"(%a, %b) : (i32, i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: RISC-V gMIR word operations require i64 operands and result
