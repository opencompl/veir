// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (i64, i32, i16, i8, i5) -> (), sym_name = "main"}> ({
  ^bb0(%x_i64: i64, %x_i32: i32, %x_i16: i16, %x_i8: i8, %x_i5: i5):
    // `i64` is legal.
    %ctlz64 = "gmir.g_ctlz"(%x_i64) : (i64) -> i64
    // CHECK:      "gmir.g_ctlz"(%{{.*}}) : (i64) -> i64
    %cttz64 = "gmir.g_cttz"(%x_i64) : (i64) -> i64
    // CHECK-NEXT: "gmir.g_cttz"(%{{.*}}) : (i64) -> i64
    %ctpop64 = "gmir.g_ctpop"(%x_i64) : (i64) -> i64
    // CHECK-NEXT: "gmir.g_ctpop"(%{{.*}}) : (i64) -> i64
    %bswap64 = "gmir.g_bswap"(%x_i64) : (i64) -> i64
    // CHECK-NEXT: "gmir.g_bswap"(%{{.*}}) : (i64) -> i64
    %bitreverse64 = "gmir.g_bitreverse"(%x_i64) : (i64) -> i64
    // CHECK-NEXT: "gmir.g_bitreverse"(%{{.*}}) : (i64) -> i64
    %brev8 = "gmir.g_brev8"(%x_i64) : (i64) -> i64
    // CHECK-NEXT: "gmir.g_brev8"(%{{.*}}) : (i64) -> i64

    // The `i32` counts use the word variants.
    %ctlz32 = "gmir.g_ctlz"(%x_i32) : (i32) -> i32
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[W:.*]] = "riscv.clzw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[W]]) : (!riscv.reg) -> i32
    %cttz32 = "gmir.g_cttz"(%x_i32) : (i32) -> i32
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[W:.*]] = "riscv.ctzw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[W]]) : (!riscv.reg) -> i32

    %ctpop32 = "gmir.g_ctpop"(%x_i32) : (i32) -> i32
    // CHECK-NEXT: %[[C:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
    // CHECK-NEXT: %[[W:.*]] = "riscv.cpopw"(%[[C]]) : (!riscv.reg) -> !riscv.reg
    // CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[W]]) : (!riscv.reg) -> i32

    // `i8` counts are widened to `i32`. `ctlz` subtracts the added leading zeros and `cttz` sets
    // the bit above the operand, so that a zero operand still counts 8.
    %ctlz8 = "gmir.g_ctlz"(%x_i8) : (i8) -> i8
    // CHECK:      "gmir.g_constant"() <{"value" = 255 : i64}> : () -> i64
    // CHECK:      "gmir.g_and"
    // CHECK:      "riscv.clzw"
    // CHECK:      "gmir.g_constant"() <{"value" = 24 : i64}> : () -> i64
    // CHECK:      "riscv.subw"
    // CHECK:      "gmir.g_trunc"(%{{.*}}) : (i32) -> i8
    %cttz8 = "gmir.g_cttz"(%x_i8) : (i8) -> i8
    // CHECK:      "gmir.g_constant"() <{"value" = 256 : i64}> : () -> i64
    // CHECK:      "gmir.g_or"
    // CHECK:      "riscv.ctzw"
    // CHECK:      "gmir.g_trunc"(%{{.*}}) : (i32) -> i8

    // An `i8` `ctpop` is widened to `i32`, zero-extending its operand.
    %ctpop8 = "gmir.g_ctpop"(%x_i8) : (i8) -> i8
    // CHECK:      "gmir.g_and"
    // CHECK:      "riscv.cpopw"
    // CHECK:      "gmir.g_trunc"(%{{.*}}) : (i32) -> i8

    // Narrow reversals are done on `i64`, and the result is shifted back down.
    %bswap16 = "gmir.g_bswap"(%x_i16) : (i16) -> i16
    // CHECK:      %[[EXT:.*]] = "gmir.g_anyext"(%{{.*}}) : (i16) -> i64
    // CHECK-NEXT: %[[REV:.*]] = "gmir.g_bswap"(%[[EXT]]) : (i64) -> i64
    // CHECK-NEXT: %[[AMT:.*]] = "gmir.g_constant"() <{"value" = 48 : i64}> : () -> i64
    // CHECK-NEXT: %[[SHR:.*]] = "gmir.g_lshr"(%[[REV]], %[[AMT]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[SHR]]) : (i64) -> i16
    %bitreverse32 = "gmir.g_bitreverse"(%x_i32) : (i32) -> i32
    // CHECK-NEXT: %[[EXT:.*]] = "gmir.g_anyext"(%{{.*}}) : (i32) -> i64
    // CHECK-NEXT: %[[REV:.*]] = "gmir.g_bitreverse"(%[[EXT]]) : (i64) -> i64
    // CHECK-NEXT: %[[AMT:.*]] = "gmir.g_constant"() <{"value" = 32 : i64}> : () -> i64
    // CHECK-NEXT: %[[SHR:.*]] = "gmir.g_lshr"(%[[REV]], %[[AMT]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[SHR]]) : (i64) -> i32
    %bitreverse5 = "gmir.g_bitreverse"(%x_i5) : (i5) -> i5
    // CHECK-NEXT: %[[EXT:.*]] = "gmir.g_anyext"(%{{.*}}) : (i5) -> i64
    // CHECK-NEXT: %[[REV:.*]] = "gmir.g_bitreverse"(%[[EXT]]) : (i64) -> i64
    // CHECK-NEXT: %[[AMT:.*]] = "gmir.g_constant"() <{"value" = 59 : i64}> : () -> i64
    // CHECK-NEXT: %[[SHR:.*]] = "gmir.g_lshr"(%[[REV]], %[[AMT]]) : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[SHR]]) : (i64) -> i5

    // The `i8` bit reversal only reverses the bits within the byte.
    %bitreverse8 = "gmir.g_bitreverse"(%x_i8) : (i8) -> i8
    // CHECK-NEXT: %[[EXT:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i64
    // CHECK-NEXT: %[[REV:.*]] = "gmir.g_brev8"(%[[EXT]]) : (i64) -> i64
    // CHECK-NEXT: "gmir.g_trunc"(%[[REV]]) : (i64) -> i8

    "test.test"(%ctlz64, %cttz64, %ctpop64, %bswap64, %bitreverse64, %brev8) : (i64, i64, i64, i64, i64, i64) -> ()
    "test.test"(%ctlz32, %cttz32, %ctpop32, %bitreverse32) : (i32, i32, i32, i32) -> ()
    "test.test"(%ctlz8, %cttz8, %ctpop8, %bitreverse8, %bswap16, %bitreverse5) : (i8, i8, i8, i8, i16, i5) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
