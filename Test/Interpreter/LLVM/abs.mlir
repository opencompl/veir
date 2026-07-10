// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8)}> ({
    %cn5 = "llvm.mlir.constant"() <{ "value" = -5 : i8 }> : () -> i8
    %cmin = "llvm.mlir.constant"() <{ "value" = -128 : i8 }> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    // abs(-5) = 5 (0x05)
    %a = "llvm.intr.abs"(%cn5) <{is_int_min_poison = false}> : (i8) -> i8
    // abs(INT8_MIN) with is_int_min_poison = false -> INT8_MIN (0x80)
    %b = "llvm.intr.abs"(%cmin) <{is_int_min_poison = false}> : (i8) -> i8
    // abs(INT8_MIN) with is_int_min_poison = true -> poison
    %c = "llvm.intr.abs"(%cmin) <{is_int_min_poison = true}> : (i8) -> i8
    // abs(poison) -> poison
    %d = "llvm.intr.abs"(%poison) <{is_int_min_poison = false}> : (i8) -> i8
    "func.return"(%a, %b, %c, %d) : (i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x05#8, 0x80#8, poison, poison]
