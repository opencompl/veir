// RUN: veir-interpret %s | filecheck %s

// Only the borrow-in makes 0 - 0 wrap around in `i8`, so it borrows, while 1 - 0 - 1 just fits.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i1, i8, i1)}> ({
    %zero = "llvm.mlir.constant"() <{ "value" = 0 : i8 }> : () -> i8
    %one = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %borrow = "llvm.mlir.constant"() <{ "value" = true }> : () -> i1
    %x, %x_borrow = "gmir.g_usube"(%zero, %zero, %borrow) : (i8, i8, i1) -> (i8, i1)
    %y, %y_borrow = "gmir.g_usube"(%one, %zero, %borrow) : (i8, i8, i1) -> (i8, i1)
    "func.return"(%x, %x_borrow, %y, %y_borrow) : (i8, i1, i8, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8, 0x1#1, 0x00#8, 0x0#1]
