// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

"builtin.module"() ({
  // Both operand orders must match even when the mask has another use.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "low_word_mask"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %mask = "riscv.li"() <{"value" = 4294967295 : i64}> : () -> !riscv.reg
    %a = "riscv.and"(%x, %mask) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %b = "riscv.and"(%mask, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%a, %b, %mask) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  // Keeping bit 32 is not a word zero extension.
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "wider_mask"}> ({
  ^bb0(%x: !riscv.reg):
    %mask = "riscv.li"() <{"value" = 8589934591 : i64}> : () -> !riscv.reg
    %a = "riscv.and"(%x, %mask) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%a) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @low_word_mask(
// CHECK-SAME: %[[X:[^:]*]]: !riscv.reg, %[[Y:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[MASK:.*]] = "riscv.li"() <{"value" = 4294967295 : i64}>
// CHECK-NEXT: %[[A:.*]] = "riscv.zextw"(%[[X]])
// CHECK-NEXT: %[[B:.*]] = "riscv.zextw"(%[[Y]])
// CHECK-NEXT: "func.return"(%[[A]], %[[B]], %[[MASK]])

// CHECK-LABEL: func.func @wider_mask(
// CHECK-SAME: %[[WIDE_X:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[WIDE_MASK:.*]] = "riscv.li"() <{"value" = 8589934591 : i64}>
// CHECK-NEXT: %[[WIDE_A:.*]] = "riscv.and"(%[[WIDE_X]], %[[WIDE_MASK]])
// CHECK-NEXT: "func.return"(%[[WIDE_A]])
