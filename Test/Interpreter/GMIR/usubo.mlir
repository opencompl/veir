// RUN: veir-interpret %s | filecheck %s

// 0 - 1 just wraps around in `i8` and borrows, while 1 - 1 just fits.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1)}> ({
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %x, %x_borrow = "gmir.g_usubo"(%zero, %one) : (i8, i8) -> (i8, i1)
    %y, %y_borrow = "gmir.g_usubo"(%one, %one) : (i8, i8) -> (i8, i1)
    "func.return"(%x, %x_borrow, %y, %y_borrow) : (i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8, 0x1#1, 0x00#8, 0x0#1]
