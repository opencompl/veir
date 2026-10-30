// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=SEL < %t
// RUN: not grep -E "riscv\.(subw|zextw)\"" %t

// `sub_to_addw` turns an `i32` `sub x, C` into `addiw x, -C`, keeping `-C` sign-extended so that
// `sub x, INT32_MIN` still loads `INT32_MIN`. The `not` of an `xor` selects `xnor` at `i64` and
// `i32`. The `i8` counts are done by the word instructions on `i64`, so no `zextw` is left
// between them and the truncation.

// SEL-DAG: "riscv.addiw"(%{{.*}}) <{"value" = -5 : i64}>
// SEL-DAG: "riscv.addiw"(%{{.*}}) <{"value" = 2047 : i64}>
// SEL-DAG: "riscv.li"() <{"value" = -2147483648 : i64}>
// SEL-DAG: "riscv.li"() <{"value" = 2048 : i64}>
// SEL-DAG: "riscv.xnor"
// SEL-DAG: "riscv.xnor"
// SEL-DAG: "riscv.ctzw"
// SEL-DAG: "riscv.clzw"
// SEL-DAG: "riscv.cpopw"

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i64, i32, i8, i8, i8)}> ({
    // `llvm.freeze` hides the inputs from the constant folds of the post-legalizer combiner.
    %x0 = "llvm.mlir.constant"() <{value = 2147483632 : i32}> : () -> i32
    %y0 = "llvm.mlir.constant"() <{value = 81985529216486895 : i64}> : () -> i64
    %z0 = "llvm.mlir.constant"() <{value = -6148914691236517206 : i64}> : () -> i64
    %b0 = "llvm.mlir.constant"() <{value = 40 : i8}> : () -> i8
    %x = "llvm.freeze"(%x0) : (i32) -> i32
    %y = "llvm.freeze"(%y0) : (i64) -> i64
    %z = "llvm.freeze"(%z0) : (i64) -> i64
    %b = "llvm.freeze"(%b0) : (i8) -> i8
    %c5 = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    %r0 = "llvm.sub"(%x, %c5) : (i32, i32) -> i32
    %cmin = "llvm.mlir.constant"() <{value = -2147483648 : i32}> : () -> i32
    %r1 = "llvm.sub"(%x, %cmin) : (i32, i32) -> i32
    %cm2047 = "llvm.mlir.constant"() <{value = -2047 : i32}> : () -> i32
    %r2 = "llvm.sub"(%x, %cm2047) : (i32, i32) -> i32
    %cm2048 = "llvm.mlir.constant"() <{value = -2048 : i32}> : () -> i32
    %r3 = "llvm.sub"(%x, %cm2048) : (i32, i32) -> i32
    %m1 = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
    %xy = "llvm.xor"(%y, %z) : (i64, i64) -> i64
    %r4 = "llvm.xor"(%xy, %m1) : (i64, i64) -> i64
    %m1w = "llvm.mlir.constant"() <{value = -1 : i32}> : () -> i32
    %t = "llvm.trunc"(%y) : (i64) -> i32
    %xt = "llvm.xor"(%x, %t) : (i32, i32) -> i32
    %r5 = "llvm.xor"(%m1w, %xt) : (i32, i32) -> i32
    %r6 = "llvm.intr.cttz"(%b) <{is_zero_poison = false}> : (i8) -> i8
    %r7 = "llvm.intr.ctlz"(%b) <{is_zero_poison = false}> : (i8) -> i8
    %r8 = "llvm.intr.ctpop"(%b) : (i8) -> i8
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5, %r6, %r7, %r8) : (i32, i32, i32, i32, i64, i32, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x7fffffeb#32, 0xfffffff0#32, 0x800007ef#32, 0x800007f0#32, 0x54761032dcfe98ba#64, 0x09abcde0#32, 0x03#8, 0x02#8, 0x02#8]
