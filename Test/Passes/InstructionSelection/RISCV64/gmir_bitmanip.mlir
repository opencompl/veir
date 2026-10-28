// RUN: veir-opt %s -p=riscv | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64) -> (), sym_name = "main"}> ({
  ^bb0(%x: i64):
    %ctlz = "gmir.g_ctlz"(%x) : (i64) -> i64
    // CHECK:      %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.clz"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %cttz = "gmir.g_cttz"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.ctz"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %ctpop = "gmir.g_ctpop"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.cpop"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %bswap = "gmir.g_bswap"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.rev8"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %brev8 = "gmir.g_brev8"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.brev8"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %bitreverse = "gmir.g_bitreverse"(%x) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[B:.*]] = "riscv.brev8"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.rev8"(%[[B]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    "test.test"(%ctlz, %cttz, %ctpop, %bswap, %brev8, %bitreverse) : (i64, i64, i64, i64, i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
