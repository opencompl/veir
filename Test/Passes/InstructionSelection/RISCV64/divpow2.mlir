// RUN: veir-opt %s -p=riscv | filecheck %s

"builtin.module"() ({
    // llvm.udiv x, 8 -> riscv.srli x, 3
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f0"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
        %r = "llvm.udiv"(%a, %c) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f0(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.udiv x, 8 (i32) -> riscv.srliw x, 3
    "func.func"() <{function_type = (i32) -> i32, sym_name = "f1"}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
        %r = "llvm.udiv"(%a, %c) : (i32, i32) -> i32
        // CHECK-LABEL: func.func @f1(%{{.*}}: i32) -> i32 {
        // CHECK:       %{{.*}} = "riscv.srliw"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()

    // udiv by 2^63: its bit pattern (0x8000...0) is decoded as the negative decimal
    // -9223372036854775808, but is still a valid *unsigned* power-of-two divisor.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f2"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
        %r = "llvm.udiv"(%a, %c) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f2(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // Regression: 0xC000000000000000 (decimal -4611686018427387904) has *two* bits
    // set, so it is not a power of two -- even though its magnitude as a signed
    // `Int` (2^62) would incorrectly look like one under a naive sign/magnitude
    // check that didn't first reduce it mod 2^64. Must stay a `divu`.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f3"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = -4611686018427387904 : i64}> : () -> i64
        %r = "llvm.udiv"(%a, %c) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f3(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.li"() <{"value" = -4611686018427387904 : i64}> : () -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.divu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // Not a power of two: a plain `riscv.divu`.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f4"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
        %r = "llvm.udiv"(%a, %c) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f4(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.li"() <{"value" = 6 : i64}> : () -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.divu"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.sdiv exact x, 8 -> riscv.srai x, 3 (no negation needed)
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f5"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
        %r = "llvm.sdiv"(%a, %c) <{isExact}> : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f5(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // llvm.sdiv exact x, -8 -> riscv.srai x, 3, then negate via `sub x0, _`.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f6"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = -8 : i64}> : () -> i64
        %r = "llvm.sdiv"(%a, %c) <{isExact}> : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f6(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "rv64.get_register"() : () -> !riscv.reg<x0>
        // CHECK:       %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // i32 exact variant.
    "func.func"() <{function_type = (i32) -> i32, sym_name = "f7"}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
        %r = "llvm.sdiv"(%a, %c) <{isExact}> : (i32, i32) -> i32
        // CHECK-LABEL: func.func @f7(%{{.*}}: i32) -> i32 {
        // CHECK:       %{{.*}} = "riscv.sraiw"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()

    // General (non-exact) llvm.sdiv x, 8 -> the biased 4-instruction sequence.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f8"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
        %r = "llvm.sdiv"(%a, %c) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f8(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 61 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // General llvm.sdiv x, -8 -> the biased sequence plus a final negation.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f9"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = -8 : i64}> : () -> i64
        %r = "llvm.sdiv"(%a, %c) : (i64, i64) -> i64
        // CHECK-LABEL: func.func @f9(%{{.*}}: i64) -> i64 {
        // CHECK:       %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.srli"(%{{.*}}) <{"value" = 61 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.srai"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "rv64.get_register"() : () -> !riscv.reg<x0>
        // CHECK:       %{{.*}} = "riscv.sub"(%{{.*}}, %{{.*}}) : (!riscv.reg<x0>, !riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // i32 general variant.
    "func.func"() <{function_type = (i32) -> i32, sym_name = "f10"}> ({
    ^bb(%a: i32):
        %c = "llvm.mlir.constant"() <{value = 8 : i32}> : () -> i32
        %r = "llvm.sdiv"(%a, %c) : (i32, i32) -> i32
        // CHECK-LABEL: func.func @f10(%{{.*}}: i32) -> i32 {
        // CHECK:       %{{.*}} = "riscv.sraiw"(%{{.*}}) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.srliw"(%{{.*}}) <{"value" = 29 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.addw"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:       %{{.*}} = "riscv.sraiw"(%{{.*}}) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i32) -> ()
    }) : () -> ()
}) : () -> ()
