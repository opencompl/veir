// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=instcombine > %t.instcombine
// RUN: veir-interpret %t.instcombine | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv-combine > %t.combine
// RUN: veir-interpret %t.combine | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=isel-sdag-riscv64 > %t.sdag
// RUN: veir-interpret %t.sdag | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=isel-sdag-riscv64,isel-riscv64 > %t.isel
// RUN: veir-interpret %t.isel | filecheck %s

// Attribute widths can differ from result widths. Exercise immediate selection,
// masks, comparisons, signed/unsigned division, algebraic combines, signed min/max (including
// i1), and unsigned funnel-shift amounts at a non-power-of-two width.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i32, i8, i8, i8, i3, i3, i1, i1, i64, i64, i1, i1)}> ({
    %ten = "llvm.mlir.constant"() <{value = 10 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %minusOne = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i64
    %boolOne = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %minusTwo = "llvm.mlir.constant"() <{value = 254 : i8}> : () -> i64
    %wrappedZero = "llvm.mlir.constant"() <{value = 256 : i8}> : () -> i64
    %truncatedOne = "llvm.mlir.constant"() <{value = 4294967297 : i64}> : () -> i32
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %minusEight = "llvm.mlir.constant"() <{value = -8 : i64}> : () -> i64
    %add = "llvm.add"(%ten, %minusOne) : (i64, i64) -> i64
    %and = "llvm.and"(%ten, %minusOne) : (i64, i64) -> i64
    %or = "llvm.or"(%ten, %minusOne) : (i64, i64) -> i64
    %xor = "llvm.xor"(%ten, %minusOne) : (i64, i64) -> i64
    %shift = "llvm.shl"(%ten, %boolOne) : (i64, i64) -> i64
    %signedDiv = "llvm.sdiv"(%eight, %minusTwo) : (i64, i64) -> i64
    %signedExact = "llvm.sdiv"(%minusEight, %minusTwo) <{isExact}> : (i64, i64) -> i64
    %unsignedDiv = "llvm.udiv"(%ten, %boolOne) : (i64, i64) -> i64
    %negativeUnsigned = "llvm.udiv"(%ten, %minusOne) : (i64, i64) -> i64
    %mulBool = "llvm.mul"(%ten, %boolOne) : (i64, i64) -> i64
    %subBool = "llvm.sub"(%boolOne, %ten) : (i64, i64) -> i64
    %wrappedSub = "llvm.sub"(%ten, %wrappedZero) : (i64, i64) -> i64
    %notBool = "llvm.xor"(%ten, %boolOne) : (i64, i64) -> i64
    %falseNot = "llvm.and"(%ten, %notBool) : (i64, i64) -> i64
    %realNot = "llvm.xor"(%ten, %minusOne) : (i64, i64) -> i64
    %realNotAnd = "llvm.and"(%one, %realNot) : (i64, i64) -> i64
    %notZeroBool = "llvm.xor"(%zero, %boolOne) : (i64, i64) -> i64
    %notOneBool = "llvm.xor"(%one, %boolOne) : (i64, i64) -> i64
    %bothBool = "llvm.and"(%notZeroBool, %notOneBool) : (i64, i64) -> i64
    %allOnes = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %falseDeMorgan = "llvm.xor"(%bothBool, %allOnes) : (i64, i64) -> i64
    %smin = "llvm.intr.smin"(%ten, %minusOne) : (i64, i64) -> i64
    %smax = "llvm.intr.smax"(%ten, %minusOne) : (i64, i64) -> i64
    %one32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %truncatedAdd = "llvm.add"(%one32, %truncatedOne) : (i32, i32) -> i32
    %min8 = "llvm.mlir.constant"() <{value = 128 : i8}> : () -> i8
    %zero8 = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %one8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %signedMin8 = "llvm.intr.smin"(%min8, %zero8) : (i8, i8) -> i8
    %signedMax8 = "llvm.intr.smax"(%min8, %zero8) : (i8, i8) -> i8
    %mulNswSignBit = "llvm.mul"(%one8, %min8) <{overflowFlags = 1 : i32}> : (i8, i8) -> i8
    %seven = "llvm.mlir.constant"() <{value = 7 : i3}> : () -> i3
    %negativeTwo3 = "llvm.mlir.constant"() <{value = -2 : i3}> : () -> i3
    %one3 = "llvm.mlir.constant"() <{value = 1 : i3}> : () -> i3
    %rotateOdd = "llvm.intr.fshr"(%one3, %negativeTwo3, %seven) : (i3, i3, i3) -> i3
    %rotateOddLeft = "llvm.intr.fshl"(%one3, %negativeTwo3, %seven) : (i3, i3, i3) -> i3
    %true = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    %false = "llvm.mlir.constant"() <{value = 0 : i1}> : () -> i1
    %signedMinBool = "llvm.intr.smin"(%true, %false) : (i1, i1) -> i1
    %signedMaxBool = "llvm.intr.smax"(%true, %false) : (i1, i1) -> i1
    %selected = "llvm.select"(%true, %boolOne, %zero) : (i1, i64, i64) -> i64
    %signedCmp = "llvm.icmp"(%ten, %minusOne) <{predicate = 2 : i64}> : (i64, i64) -> i1
    %unsignedCmp = "llvm.icmp"(%ten, %boolOne) <{predicate = 6 : i64}> : (i64, i64) -> i1
    "func.return"(%add, %and, %or, %xor, %shift, %signedDiv, %signedExact, %unsignedDiv, %negativeUnsigned, %mulBool, %subBool, %wrappedSub, %falseNot, %realNotAnd, %smin, %smax, %truncatedAdd, %signedMin8, %signedMax8, %mulNswSignBit, %rotateOdd, %rotateOddLeft, %signedMinBool, %signedMaxBool, %selected, %falseDeMorgan, %signedCmp, %unsignedCmp) : (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i64, i32, i8, i8, i8, i3, i3, i1, i1, i64, i64, i1, i1) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000009#64, 0x000000000000000a#64, 0xffffffffffffffff#64, 0xfffffffffffffff5#64, 0x0000000000000014#64, 0xfffffffffffffffc#64, 0x0000000000000004#64, 0x000000000000000a#64, 0x0000000000000000#64, 0x000000000000000a#64, 0xfffffffffffffff7#64, 0x000000000000000a#64, 0x000000000000000a#64, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x000000000000000a#64, 0x00000002#32, 0x80#8, 0x00#8, 0x80#8, 0x7#3, 0x3#3, 0x1#1, 0x0#1, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x0#1, 0x0#1]
