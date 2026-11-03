// RUN: veir-interpret %s | filecheck %s

// Signed/unsigned min and max. Operands a = 5 (0x05), b = -3 (0xfd = 253).
// maxsi = 5, minsi = -3, maxui = 253, minui = 5.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %a = "arith.constant"() <{ "value" = 5 : i8 }> : () -> i8
    %b = "arith.constant"() <{ "value" = -3 : i8 }> : () -> i8
    %maxs = "arith.maxsi"(%a, %b) : (i8, i8) -> i8
    %mins = "arith.minsi"(%a, %b) : (i8, i8) -> i8
    %maxu = "arith.maxui"(%a, %b) : (i8, i8) -> i8
    %minu = "arith.minui"(%a, %b) : (i8, i8) -> i8
    "func.return"(%maxs, %mins, %maxu, %minu) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x05#8, 0xfd#8, 0xfd#8, 0x05#8]
