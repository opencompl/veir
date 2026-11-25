// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s -p=riscv > %t.riscv
// RUN: filecheck %s --check-prefix=ASM < %t.riscv
// RUN: veir-interpret %t.riscv | filecheck %s

// MLIR prints `case_values` with more than 100 elements as raw little-endian hex data, one
// `ceil(W / 8)`-byte chunk per element. These switches use that form for i32 cases 1, 2 and 5;
// an i17 case -3 (three bytes, 0x1FFFD); an i1 case `true` (one byte); and an i64 case
// 0x0123456789ABCDEF.
//
// i in 0..8: i32 key hits on i = 1, 2, 5; i17 key i - 4 hits on i = 1; i1 key hits on odd i;
// the i64 key 0x0123456789ABCDE8 + i hits on i = 7.

// CHECK: Program output: #[0x{{0*}}132b51#64]
// ASM-NOT: "llvm.switch"
// ASM: "riscv_cf.beq"

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
  ^entry:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %four = "llvm.mlir.constant"() <{value = 4 : i32}> : () -> i32
    %s0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %b1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %b2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %b3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %b4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %b5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %b6 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %factor = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %base = "llvm.mlir.constant"() <{value = 81985529216486888 : i64}> : () -> i64
    "llvm.br"(%zero, %s0) [^loop] : (i32, i64) -> ()
  ^loop(%i: i32, %sum: i64):
    "llvm.switch"(%i, %s0, %b1, %b2, %b3) [^k17, ^k17, ^k17, ^k17]
      <{case_operand_segments = array<i32: 1, 1, 1>, case_values = dense<"0x010000000200000005000000"> : vector<3xi32>,
        operandSegmentSizes = array<i32: 1, 1, 3>}> : (i32, i64, i64, i64, i64) -> ()
  ^k17(%v32: i64):
    %im4 = "llvm.sub"(%i, %four) : (i32, i32) -> i32
    %key17 = "llvm.trunc"(%im4) : (i32) -> i17
    "llvm.switch"(%key17, %v32, %b4) [^k1, ^k1]
      <{case_operand_segments = array<i32: 1>, case_values = dense<"0xFDFF01"> : vector<1xi17>,
        operandSegmentSizes = array<i32: 1, 1, 1>}> : (i17, i64, i64) -> ()
  ^k1(%v17: i64):
    %key1 = "llvm.trunc"(%i) : (i32) -> i1
    "llvm.switch"(%key1, %s0, %b5) [^k64, ^k64]
      <{case_operand_segments = array<i32: 1>, case_values = dense<"0x01"> : vector<1xi1>,
        operandSegmentSizes = array<i32: 1, 1, 1>}> : (i1, i64, i64) -> ()
  ^k64(%v1: i64):
    %iw = "llvm.zext"(%i) : (i32) -> i64
    %key64 = "llvm.add"(%iw, %base) : (i64, i64) -> i64
    "llvm.switch"(%key64, %s0, %b6) [^acc, ^acc]
      <{case_operand_segments = array<i32: 1>, case_values = dense<"0xEFCDAB8967452301"> : vector<1xi64>,
        operandSegmentSizes = array<i32: 1, 1, 1>}> : (i64, i64, i64) -> ()
  ^acc(%v64: i64):
    %t0 = "llvm.add"(%v32, %v17) : (i64, i64) -> i64
    %t1 = "llvm.add"(%t0, %v1) : (i64, i64) -> i64
    %t2 = "llvm.add"(%t1, %v64) : (i64, i64) -> i64
    %scaled = "llvm.mul"(%sum, %factor) : (i64, i64) -> i64
    %nextSum = "llvm.add"(%scaled, %t2) : (i64, i64) -> i64
    %next = "llvm.add"(%i, %one) : (i32, i32) -> i32
    "llvm.switch"(%next, %next, %nextSum, %nextSum) [^loop, ^exit]
      <{case_operand_segments = array<i32: 1>, case_values = dense<8> : vector<1xi32>,
        operandSegmentSizes = array<i32: 1, 2, 1>}> : (i32, i32, i64, i64) -> ()
  ^exit(%result: i64):
    "llvm.return"(%result) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
