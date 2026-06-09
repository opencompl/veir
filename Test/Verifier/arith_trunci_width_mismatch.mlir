// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %x = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %trunc = "arith.trunci"(%x) : (i8) -> i8
    "func.return"(%trunc) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.trunci: Result's width must be smaller than operand's width
