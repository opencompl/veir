// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// Edge cases of division by a constant power of two, lowered by the post-legalizer combines
// (no constant folding runs first): `-1`, the minimum signed value, an unsigned `2^63`/`2^31`,
// and `exact` at `i32` (a single `sraiw`, then a negation).

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i32, i32, i32, i32)}> ({
    %x = "llvm.mlir.constant"() <{value = -9223372036854775807 : i64}> : () -> i64
    %cm1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %cmin = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    %r0 = "llvm.sdiv"(%x, %cm1) : (i64, i64) -> i64
    %r1 = "llvm.sdiv"(%cmin, %cmin) : (i64, i64) -> i64
    %r2 = "llvm.sdiv"(%x, %cmin) : (i64, i64) -> i64
    %r3 = "llvm.udiv"(%x, %cmin) : (i64, i64) -> i64
    %y = "llvm.mlir.constant"() <{value = -24 : i32}> : () -> i32
    %wmin = "llvm.mlir.constant"() <{value = -2147483648 : i32}> : () -> i32
    %cm8 = "llvm.mlir.constant"() <{value = -8 : i32}> : () -> i32
    %s0 = "llvm.sdiv"(%wmin, %wmin) : (i32, i32) -> i32
    %s1 = "llvm.sdiv"(%y, %wmin) : (i32, i32) -> i32
    %s2 = "llvm.udiv"(%y, %wmin) : (i32, i32) -> i32
    %s3 = "llvm.sdiv"(%y, %cm8) <{isExact}> : (i32, i32) -> i32
    "func.return"(%r0, %r1, %r2, %r3, %s0, %s1, %s2, %s3) : (i64, i64, i64, i64, i32, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x7fffffffffffffff#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x00000001#32, 0x00000000#32, 0x00000001#32, 0x00000003#32]
// CHECK: Program output: #[0x7fffffffffffffff#64, 0x0000000000000001#64, 0x0000000000000000#64, 0x0000000000000001#64, 0x00000001#32, 0x00000000#32, 0x00000001#32, 0x00000003#32]
