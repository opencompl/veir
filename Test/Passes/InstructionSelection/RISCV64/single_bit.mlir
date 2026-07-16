// RUN: veir-opt %s -p=isel-sdag-riscv64 | filecheck %s

// Zbs single-bit immediate selection. `or`/`xor`/`and` against a constant whose
// (complemented, for bclri) value is a single set bit selects to bseti/binvi/bclri,
// emitting the bit index. These only fire when the immediate does not fit a signed
// 12-bit field, so ori/andi/xori win the small-immediate cases. `bexti` recognizes
// `and (lshr x n) 1`.

"builtin.module"() ({
    // or x (1 << 40) -> riscv.bseti x 40
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f0"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 1099511627776 : i64}> : () -> i64
        %r = "llvm.or"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.bseti"(%{{.*}}) <{"value" = 40 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // xor x (1 << 40) -> riscv.binvi x 40
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f1"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 1099511627776 : i64}> : () -> i64
        %r = "llvm.xor"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.binvi"(%{{.*}}) <{"value" = 40 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // and x (~(1 << 40)) -> riscv.bclri x 40
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f2"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = -1099511627777 : i64}> : () -> i64
        %r = "llvm.and"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.bclri"(%{{.*}}) <{"value" = 40 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // and (lshr x 5) 1 -> riscv.bexti x 5
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f3"}> ({
    ^bb(%a: i64):
        %sh = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
        %srl = "llvm.lshr"(%a, %sh) : (i64, i64) -> i64
        %r = "llvm.and"(%srl, %one) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.bexti"(%{{.*}}) <{"value" = 5 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()

    // Single-bit mask that DOES fit imm12: handled by ori, not bseti.
    "func.func"() <{function_type = (i64) -> i64, sym_name = "f4"}> ({
    ^bb(%a: i64):
        %c = "llvm.mlir.constant"() <{value = 1024 : i64}> : () -> i64
        %r = "llvm.or"(%a, %c) : (i64, i64) -> i64
        // CHECK:      %{{.*}} = "riscv.ori"(%{{.*}}) <{"value" = 1024 : i64}> : (!riscv.reg) -> !riscv.reg
        "func.return"(%r) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
