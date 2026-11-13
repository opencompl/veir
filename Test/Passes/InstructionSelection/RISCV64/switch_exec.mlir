// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s -p=llvm-to-gmir > %t.gmir && veir-interpret %t.gmir | filecheck %s
// RUN: veir-opt %s -p=riscv > %t.riscv
// RUN: filecheck %s --check-prefix=ASM < %t.riscv
// RUN: veir-interpret %t.riscv | filecheck %s
// RUN: veir2mir %t.riscv > %t.mir

// Exercise every i8 bit pattern, including -1, the first/middle/last cases and the default.
// All edges share a destination but forward different argument pairs. The rolling checksum
// is order-sensitive, so assigning one case's arguments to another case changes the result.
// Also exercise a switch backedge with block arguments and an empty switch on exit.
// CHECK: Program output: #[0x25d68f577c5cdc42#64]
// ASM-NOT: "llvm.switch"
// ASM: "riscv_cf.beq"
// ASM-NOT: "llvm.switch"

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
  ^entry:
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %s0 = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %hundred = "llvm.mlir.constant"() <{value = 100 : i64}> : () -> i64
    %a = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %c = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %d = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %e = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %factor = "llvm.mlir.constant"() <{value = 31 : i64}> : () -> i64
    "llvm.br"(%zero, %s0) [^loop] : (i32, i64) -> ()
  ^loop(%i: i32, %sum: i64):
    %key = "llvm.trunc"(%i) : (i32) -> i8
    "llvm.switch"(%key, %hundred, %e, %hundred, %a, %hundred, %b, %hundred, %c, %hundred, %d)
      [^dispatch, ^dispatch, ^dispatch, ^dispatch, ^dispatch]
      <{case_operand_segments = array<i32: 2, 2, 2, 2>, case_values = dense<[-1, 0, 5, 6]> : vector<4xi8>,
        operandSegmentSizes = array<i32: 1, 2, 8>}> : (i8, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) -> ()
  ^dispatch(%x: i64, %y: i64):
    %r = "llvm.sub"(%x, %y) : (i64, i64) -> i64
    %scaled = "llvm.mul"(%sum, %factor) : (i64, i64) -> i64
    %nextSum = "llvm.add"(%scaled, %r) : (i64, i64) -> i64
    %next = "llvm.add"(%i, %one) : (i32, i32) -> i32
    "llvm.switch"(%next, %next, %nextSum, %nextSum) [^loop, ^exit]
      <{case_operand_segments = array<i32: 1>, case_values = dense<256> : vector<1xi32>,
        operandSegmentSizes = array<i32: 1, 2, 1>}> : (i32, i32, i64, i64) -> ()
  ^exit(%result: i64):
    "llvm.switch"(%result, %result) [^return]
      <{case_operand_segments = array<i32>, operandSegmentSizes = array<i32: 1, 1, 0>}> : (i64, i64) -> ()
  ^return(%answer: i64):
    "llvm.return"(%answer) : (i64) -> ()
  }) : () -> ()
}) : () -> ()
