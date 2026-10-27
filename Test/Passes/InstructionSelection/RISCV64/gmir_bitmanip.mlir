// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i32) -> (), sym_name = "main"}> ({
  ^bb0(%x: i64, %y: i32):
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
    // The count of a zero-extended `i32` only counts its low 32 bits. The extension has another
    // user, so it is still selected.
    %zext = "gmir.g_zext"(%y) : (i32) -> i64
    %cpopw_zext = "gmir.g_ctpop"(%zext) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.zextw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.cpopw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    %mask = "gmir.g_constant"() <{value = 0xffffffff : i64}> : () -> i64
    %and = "gmir.g_and"(%x, %mask) : (i64, i64) -> i64
    %cpopw_and = "gmir.g_ctpop"(%and) : (i64) -> i64
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
    // CHECK-NEXT: %[[R:.*]] = "riscv.cpopw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
    // Another mask keeps more bits than `cpopw` counts.
    %mask33 = "gmir.g_constant"() <{value = 0x1ffffffff : i64}> : () -> i64
    %and33 = "gmir.g_and"(%x, %mask33) : (i64, i64) -> i64
    %cpop_and33 = "gmir.g_ctpop"(%and33) : (i64) -> i64
    // CHECK-NOT:  "riscv.cpopw"
    // CHECK:      "riscv.cpop"
    "test.test"(%ctlz, %cttz, %ctpop, %bswap, %brev8, %bitreverse) : (i64, i64, i64, i64, i64, i64) -> ()
    "test.test"(%zext, %cpopw_zext, %cpopw_and, %cpop_and33) : (i64, i64, i64, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
