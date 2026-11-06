// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// The compiled code gives the same sums, carries and borrows, both for results that just wrap
// around and for results that just fit.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i1, i64, i1, i64, i1, i64, i1, i64, i1, i64, i1, i64, i1, i64, i1)}> ({
    %max = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %below_max = "llvm.mlir.constant"() <{value = -2 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %true = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %uaddo_wrap, %uaddo_wrap_carry = "gmir.g_uaddo"(%max, %one) : (i64, i64) -> (i64, i1)
    %uaddo_fit, %uaddo_fit_carry = "gmir.g_uaddo"(%below_max, %one) : (i64, i64) -> (i64, i1)
    %uadde_wrap, %uadde_wrap_carry = "gmir.g_uadde"(%max, %zero, %true) : (i64, i64, i1) -> (i64, i1)
    %uadde_fit, %uadde_fit_carry = "gmir.g_uadde"(%below_max, %zero, %true) : (i64, i64, i1) -> (i64, i1)
    %usubo_wrap, %usubo_wrap_borrow = "gmir.g_usubo"(%zero, %one) : (i64, i64) -> (i64, i1)
    %usubo_fit, %usubo_fit_borrow = "gmir.g_usubo"(%one, %one) : (i64, i64) -> (i64, i1)
    %usube_wrap, %usube_wrap_borrow = "gmir.g_usube"(%zero, %zero, %true) : (i64, i64, i1) -> (i64, i1)
    %usube_fit, %usube_fit_borrow = "gmir.g_usube"(%one, %zero, %true) : (i64, i64, i1) -> (i64, i1)
    "func.return"(%uaddo_wrap, %uaddo_wrap_carry, %uaddo_fit, %uaddo_fit_carry, %uadde_wrap, %uadde_wrap_carry, %uadde_fit, %uadde_fit_carry, %usubo_wrap, %usubo_wrap_borrow, %usubo_fit, %usubo_fit_borrow, %usube_wrap, %usube_wrap_borrow, %usube_fit, %usube_fit_borrow) : (i64, i1, i64, i1, i64, i1, i64, i1, i64, i1, i64, i1, i64, i1, i64, i1) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000000#64, 0x1#1, 0xffffffffffffffff#64, 0x0#1, 0x0000000000000000#64, 0x1#1, 0xffffffffffffffff#64, 0x0#1, 0xffffffffffffffff#64, 0x1#1, 0x0000000000000000#64, 0x0#1, 0xffffffffffffffff#64, 0x1#1, 0x0000000000000000#64, 0x0#1]
// CHECK: Program output: #[0x0000000000000000#64, 0x1#1, 0xffffffffffffffff#64, 0x0#1, 0x0000000000000000#64, 0x1#1, 0xffffffffffffffff#64, 0x0#1, 0xffffffffffffffff#64, 0x1#1, 0x0000000000000000#64, 0x0#1, 0xffffffffffffffff#64, 0x1#1, 0x0000000000000000#64, 0x0#1]
