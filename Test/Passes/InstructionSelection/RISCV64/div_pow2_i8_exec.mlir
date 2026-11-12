// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

// XFAIL: *
// Needs `lowerSext`, commented out of the pass as unproven.

// `i8` divisions by a power of two become shifts before legalization, including by `-2^7`.
// `sdiv` rounds toward zero, so `0xff / 2` is 0.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8, i8, i8, i8, i8, i8, i8)}> ({
    // 0x80
    %min = "llvm.mlir.constant"() <{value = -128 : i8}> : () -> i8
    // 0xff
    %neg_one = "llvm.mlir.constant"() <{value = -1 : i8}> : () -> i8
    %two = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %neg_two = "llvm.mlir.constant"() <{value = -2 : i8}> : () -> i8
    %a = "llvm.sdiv"(%min, %two) : (i8, i8) -> i8
    %b = "llvm.sdiv"(%neg_one, %two) : (i8, i8) -> i8
    %c = "llvm.sdiv"(%min, %neg_two) : (i8, i8) -> i8
    %d = "llvm.sdiv"(%neg_one, %neg_two) : (i8, i8) -> i8
    %e = "llvm.sdiv"(%min, %min) : (i8, i8) -> i8
    %f = "llvm.sdiv"(%neg_one, %min) : (i8, i8) -> i8
    %g = "llvm.udiv"(%min, %min) : (i8, i8) -> i8
    %h = "llvm.udiv"(%neg_one, %min) : (i8, i8) -> i8
    "func.return"(%a, %b, %c, %d, %e, %f, %g, %h) : (i8, i8, i8, i8, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:       Program output: #[0xc0#8, 0x00#8, 0x40#8, 0x00#8, 0x01#8, 0x00#8, 0x01#8, 0x01#8]
// CHECK-NOT: "riscv.div
// CHECK:     Program output: #[0xc0#8, 0x00#8, 0x40#8, 0x00#8, 0x01#8, 0x00#8, 0x01#8, 0x01#8]
