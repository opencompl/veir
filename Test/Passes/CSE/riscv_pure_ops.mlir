// RUN: veir-opt %s -p=cse --allow-unregistered-dialect | filecheck %s

// `cse` also recognizes pure RISC-V register ops (Veir/Passes/CSE.lean), not
// just the LLVM dialect.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> ()}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    // Commutative: swapped operands merge too.
    %and0 = "riscv.and"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %and1 = "riscv.and"(%y, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %xor0 = "riscv.xor"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %xor1 = "riscv.xor"(%y, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %add0 = "riscv.add"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %add1 = "riscv.add"(%y, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "test.test"(%and0, %and1, %xor0, %xor1, %add0, %add1) :
        (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // CHECK:      ^{{.*}}(%[[X:.*]] : !riscv.reg, %[[Y:.*]] : !riscv.reg):
    // CHECK-NEXT: %[[AND:.*]] = "riscv.and"(%[[X]], %[[Y]])
    // CHECK-NEXT: %[[XOR:.*]] = "riscv.xor"(%[[X]], %[[Y]])
    // CHECK-NEXT: %[[ADD:.*]] = "riscv.add"(%[[X]], %[[Y]])
    // CHECK-NEXT: "test.test"(%[[AND]], %[[AND]], %[[XOR]], %[[XOR]], %[[ADD]], %[[ADD]])

    // Non-commutative: swapped operands stay distinct.
    %sub0 = "riscv.sub"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sub1 = "riscv.sub"(%x, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sub_swap = "riscv.sub"(%y, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "test.test"(%sub0, %sub1, %sub_swap) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // CHECK-NEXT: %[[SUB:.*]] = "riscv.sub"(%[[X]], %[[Y]])
    // CHECK-NEXT: %[[SUB_SWAP:.*]] = "riscv.sub"(%[[Y]], %[[X]])
    // CHECK-NEXT: "test.test"(%[[SUB]], %[[SUB]], %[[SUB_SWAP]])

    // Unary op duplicates merge.
    %zx0 = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zx1 = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %sx0 = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    %sx1 = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    "test.test"(%zx0, %zx1, %sx0, %sx1) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // CHECK-NEXT: %[[ZX:.*]] = "riscv.zextw"(%[[X]])
    // CHECK-NEXT: %[[SX:.*]] = "riscv.sextw"(%[[X]])
    // CHECK-NEXT: "test.test"(%[[ZX]], %[[ZX]], %[[SX]], %[[SX]])

    // Same op, different immediates: stay distinct.
    %ror7_0 = "riscv.roriw"(%x) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    %ror7_1 = "riscv.roriw"(%x) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    %ror18 = "riscv.roriw"(%x) <{"value" = 18 : i64}> : (!riscv.reg) -> !riscv.reg
    "test.test"(%ror7_0, %ror7_1, %ror18) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // CHECK-NEXT: %[[ROR7:.*]] = "riscv.roriw"(%[[X]]) <{"value" = 7 : i64}>
    // CHECK-NEXT: %[[ROR18:.*]] = "riscv.roriw"(%[[X]]) <{"value" = 18 : i64}>
    // CHECK-NEXT: "test.test"(%[[ROR7]], %[[ROR7]], %[[ROR18]])

    // Same-valued constants merge; different-typed/valued ones don't.
    %c0 = "riscv.li"() <{"value" = 63 : i32}> : () -> !riscv.reg
    %c1 = "riscv.li"() <{"value" = 63 : i32}> : () -> !riscv.reg
    %c2 = "riscv.li"() <{"value" = 64 : i32}> : () -> !riscv.reg
    "test.test"(%c0, %c1, %c2) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()

    // CHECK-NEXT: %[[C63:.*]] = "riscv.li"() <{"value" = 63 : i32}>
    // CHECK-NEXT: %[[C64:.*]] = "riscv.li"() <{"value" = 64 : i32}>
    // CHECK-NEXT: "test.test"(%[[C63]], %[[C63]], %[[C64]])

    // `riscv.sw` has no result and must never be treated as CSE-able (it's
    // memory-effecting; two `sw`s to the same address are not one write).
    "riscv.sw"(%x, %y) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    "riscv.sw"(%x, %y) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()

    // CHECK-NEXT: "riscv.sw"(%[[X]], %[[Y]]) <{"value" = 0 : i64}>
    // CHECK-NEXT: "riscv.sw"(%[[X]], %[[Y]]) <{"value" = 0 : i64}>

    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
