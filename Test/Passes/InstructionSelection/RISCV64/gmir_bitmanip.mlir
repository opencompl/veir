// RUN: veir-opt %s -p=riscv | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i32) -> (), sym_name = "main"}> ({
  ^bb0(%x: i64, %y: i32):
    %ctlz = "gmir.g_ctlz"(%x) : (i64) -> i64
    // CHECK:      %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.clz"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %cttz = "gmir.g_cttz"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[R:.*]] = "riscv.ctz"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %ctpop = "gmir.g_ctpop"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[R:.*]] = "riscv.cpop"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %bswap = "gmir.g_bswap"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[R:.*]] = "riscv.rev8"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %brev8 = "gmir.g_brev8"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[BREV8:.*]] = "riscv.brev8"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[BREV8]]) : (!riscv.reg) -> i64
    // `cse` reuses the `brev8` of `%brev8`.
    %bitreverse = "gmir.g_bitreverse"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[R:.*]] = "riscv.rev8"(%[[BREV8]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %clzw = "gmir_riscv.g_clzw"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[R:.*]] = "riscv.clzw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %ctzw = "gmir_riscv.g_ctzw"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[R:.*]] = "riscv.ctzw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    // `cpopw` counts the low 32 bits, so it needs no zero extension.
    %zext = "gmir.g_zext"(%y) : (i32) -> i64
    %cpopw = "gmir.g_ctpop"(%zext) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.cpopw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    "test.test"(%ctlz, %cttz, %ctpop, %bswap, %brev8, %bitreverse) : (i64, i64, i64, i64, i64, i64) -> ()
    "test.test"(%clzw, %ctzw, %cpopw) : (i64, i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
