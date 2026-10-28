// RUN: veir-interpret %s | filecheck %s

// 255 + 1 just wraps around in `i8` and carries, while 254 + 1 just fits.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1)}> ({
    %max = "llvm.mlir.constant"() <{ "value" = 255 : i8 }> : () -> i8
    %below_max = "llvm.mlir.constant"() <{ "value" = 254 : i8 }> : () -> i8
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %x, %x_carry = "gmir.g_uaddo"(%max, %one) : (i8, i8) -> (i8, i1)
    %y, %y_carry = "gmir.g_uaddo"(%below_max, %one) : (i8, i8) -> (i8, i1)
    "func.return"(%x, %x_carry, %y, %y_carry) : (i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00#8, 0x1#1, 0xff#8, 0x0#1]
