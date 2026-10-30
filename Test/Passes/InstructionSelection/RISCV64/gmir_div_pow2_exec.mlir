// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64,postlegalizer-combiner-riscv64,isel-br-riscv64,isel-riscv64,isel-abi-riscv64,reconcile-cast,riscv-combine,dce > %t
// RUN: veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=SEL < %t

// Power-of-two divisions, selected through the post-legalizer combines: negative dividends, negative and minimum-value divisors, `exact`, and the
// i32 word forms, including the unsigned `2^31` and `2^63` divisors.

// SEL-NOT: "riscv.div
// SEL-NOT: "riscv.rem

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32, i32, i64, i64, i64, i64, i64, i64)}> ({
    %x = "llvm.mlir.constant"() <{value = -7 : i32}> : () -> i32
    %m16 = "llvm.mlir.constant"() <{value = -16 : i32}> : () -> i32
    %min = "llvm.mlir.constant"() <{value = -2147483648 : i32}> : () -> i32
    %c8 = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
    %cm8 = "llvm.mlir.constant"() <{value = -8 : i32}> : () -> i32
    %c2 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %a0 = "llvm.sdiv"(%x, %c8) : (i32, i32) -> i32
    %a1 = "llvm.sdiv"(%x, %cm8) : (i32, i32) -> i32
    %a2 = "llvm.sdiv"(%min, %min) : (i32, i32) -> i32
    %a3 = "llvm.sdiv"(%m16, %cm8) <{isExact}> : (i32, i32) -> i32
    %a4 = "llvm.udiv"(%x, %min) : (i32, i32) -> i32
    %a5 = "llvm.sdiv"(%x, %c2) : (i32, i32) -> i32
    %a6 = "llvm.udiv"(%x, %c8) : (i32, i32) -> i32
    %y = "llvm.mlir.constant"() <{value = -7 : i64}> : () -> i64
    %ymin = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %d8 = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %dm8 = "llvm.mlir.constant"() <{value = -8 : i64}> : () -> i64
    %b0 = "llvm.sdiv"(%y, %d8) : (i64, i64) -> i64
    %b1 = "llvm.sdiv"(%y, %dm8) : (i64, i64) -> i64
    %b2 = "llvm.sdiv"(%ymin, %ymin) : (i64, i64) -> i64
    %b3 = "llvm.udiv"(%y, %ymin) : (i64, i64) -> i64
    %b4 = "llvm.sdiv"(%y, %ymin) : (i64, i64) -> i64
    %y16 = "llvm.mlir.constant"() <{value = -16 : i64}> : () -> i64
    %b5 = "llvm.sdiv"(%y16, %dm8) <{isExact}> : (i64, i64) -> i64
    "func.return"(%a0, %a1, %a2, %a3, %a4, %a5, %a6, %b0, %b1, %b2, %b3, %b4, %b5) : (i32, i32, i32, i32, i32, i32, i32, i64, i64, i64, i64, i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000#32, 0x00000000#32, 0x00000001#32, 0x00000002#32, 0x00000001#32, 0xfffffffd#32, 0x1fffffff#32, 0x0000000000000000#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000002#64]
