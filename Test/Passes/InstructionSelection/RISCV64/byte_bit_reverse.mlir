// RUN: veir-opt %s --print-op-generic -p=isel-riscv64,dce | filecheck %s

"builtin.module"() ({
  // CHECK-LABEL: "sym_name" = "bswap_bitreverse_16"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i16) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i16
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bswap_bitreverse_16", function_type = (i16) -> i16}> ({
  ^bb0(%x: i16):
    %inner = "llvm.intr.bitreverse"(%x) : (i16) -> i16
    %r = "llvm.intr.bswap"(%inner) : (i16) -> i16
    "func.return"(%r) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bitreverse_bswap_16"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i16) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i16
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bitreverse_bswap_16", function_type = (i16) -> i16}> ({
  ^bb0(%x: i16):
    %inner = "llvm.intr.bswap"(%x) : (i16) -> i16
    %r = "llvm.intr.bitreverse"(%inner) : (i16) -> i16
    "func.return"(%r) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bswap_bitreverse_32"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i32
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bswap_bitreverse_32", function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %inner = "llvm.intr.bitreverse"(%x) : (i32) -> i32
    %r = "llvm.intr.bswap"(%inner) : (i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bitreverse_bswap_32"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i32
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bitreverse_bswap_32", function_type = (i32) -> i32}> ({
  ^bb0(%x: i32):
    %inner = "llvm.intr.bswap"(%x) : (i32) -> i32
    %r = "llvm.intr.bitreverse"(%inner) : (i32) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bswap_bitreverse_64"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bswap_bitreverse_64", function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %inner = "llvm.intr.bitreverse"(%x) : (i64) -> i64
    %r = "llvm.intr.bswap"(%inner) : (i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bitreverse_bswap_64"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[R]]) : (!riscv.reg) -> i64
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bitreverse_bswap_64", function_type = (i64) -> i64}> ({
  ^bb0(%x: i64):
    %inner = "llvm.intr.bswap"(%x) : (i64) -> i64
    %r = "llvm.intr.bitreverse"(%inner) : (i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bitreverse_8"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i8) -> !riscv.reg
  // CHECK-NEXT: %[[B:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[B]]) : (!riscv.reg) -> i8
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bitreverse_8", function_type = (i8) -> i8}> ({
  ^bb0(%x: i8):
    %r = "llvm.intr.bitreverse"(%x) : (i8) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bswap_16"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i16) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.rev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[S:.*]] = "riscv.srli"(%[[R]]) <{"value" = 48 : i64}> : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[S]]) : (!riscv.reg) -> i16
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bswap_16", function_type = (i16) -> i16}> ({
  ^bb0(%x: i16):
    %r = "llvm.intr.bswap"(%x) : (i16) -> i16
    "func.return"(%r) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "bitreverse_16"
  // CHECK: %[[X:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i16) -> !riscv.reg
  // CHECK-NEXT: %[[B:.*]] = "riscv.brev8"(%[[X]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[R:.*]] = "riscv.rev8"(%[[B]]) : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[S:.*]] = "riscv.srli"(%[[R]]) <{"value" = 48 : i64}> : (!riscv.reg) -> !riscv.reg
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[S]]) : (!riscv.reg) -> i16
  // CHECK-NEXT: "func.return"(%[[OUT]])
  "func.func"() <{sym_name = "bitreverse_16", function_type = (i16) -> i16}> ({
  ^bb0(%x: i16):
    %r = "llvm.intr.bitreverse"(%x) : (i16) -> i16
    "func.return"(%r) : (i16) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "shared_bitreverse"
  // CHECK: "riscv.rev8"
  // CHECK: %[[DIRECT:.*]] = "riscv.brev8"
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[DIRECT]])
  // CHECK-NEXT: "func.return"(%{{.*}}, %[[OUT]])
  "func.func"() <{sym_name = "shared_bitreverse", function_type = (i32) -> (i32, i32)}> ({
  ^bb0(%x: i32):
    %inner = "llvm.intr.bitreverse"(%x) : (i32) -> i32
    %r = "llvm.intr.bswap"(%inner) : (i32) -> i32
    "func.return"(%inner, %r) : (i32, i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "shared_bswap"
  // CHECK: "riscv.rev8"
  // CHECK: %[[DIRECT:.*]] = "riscv.brev8"
  // CHECK-NEXT: %[[OUT:.*]] = "builtin.unrealized_conversion_cast"(%[[DIRECT]])
  // CHECK-NEXT: "func.return"(%{{.*}}, %[[OUT]])
  "func.func"() <{sym_name = "shared_bswap", function_type = (i32) -> (i32, i32)}> ({
  ^bb0(%x: i32):
    %inner = "llvm.intr.bswap"(%x) : (i32) -> i32
    %r = "llvm.intr.bitreverse"(%inner) : (i32) -> i32
    "func.return"(%inner, %r) : (i32, i32) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "unsupported_7"
  // CHECK: "llvm.intr.bitreverse"
  "func.func"() <{sym_name = "unsupported_7", function_type = (i7) -> i7}> ({
  ^bb0(%x: i7):
    %r = "llvm.intr.bitreverse"(%x) : (i7) -> i7
    "func.return"(%r) : (i7) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "unsupported_128"
  // CHECK: "llvm.intr.bitreverse"
  "func.func"() <{sym_name = "unsupported_128", function_type = (i128) -> i128}> ({
  ^bb0(%x: i128):
    %r = "llvm.intr.bitreverse"(%x) : (i128) -> i128
    "func.return"(%r) : (i128) -> ()
  }) : () -> ()
}) : () -> ()
