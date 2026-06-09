// RUN: not veir-opt %s 2>&1 | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %x = "arith.constant"() <{ "value" = 3 : i8 }> : () -> i8
    %ext = "arith.extui"(%x) : (i8) -> i8
    "func.return"(%ext) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: arith.extui: Operand's width must be smaller than result's width
