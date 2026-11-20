// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "f0"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %sum = "riscv.addw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%sum) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "f1"}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.addiw"(%zx) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "f2"}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.roriw"(%zx) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "f3"}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.srliw"(%zx) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "f4"}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.sextw"(%zx) : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()

// Binary word instructions.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "binary"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %0 = "riscv.subw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %1 = "riscv.mulw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %2 = "riscv.divw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %3 = "riscv.divuw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %4 = "riscv.remw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %5 = "riscv.remuw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %6 = "riscv.sllw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %7 = "riscv.srlw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %8 = "riscv.sraw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %9 = "riscv.rolw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %10 = "riscv.rorw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%0, %1, %2, %3, %4, %5, %6, %7, %8, %9, %10) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// Unary word instructions.
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "unary"}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %0 = "riscv.sraiw"(%zx) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %1 = "riscv.slliuw"(%zx) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    %2 = "riscv.clzw"(%zx) : (!riscv.reg) -> !riscv.reg
    %3 = "riscv.ctzw"(%zx) : (!riscv.reg) -> !riscv.reg
    %4 = "riscv.cpopw"(%zx) : (!riscv.reg) -> !riscv.reg
    "func.return"(%0, %1, %2, %3, %4) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// Only one operand extended, or the operands extended differently.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "operands"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %sy = "riscv.sextw"(%y) : (!riscv.reg) -> !riscv.reg
    %0 = "riscv.addw"(%zx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %1 = "riscv.addw"(%x, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %2 = "riscv.addw"(%zx, %sy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%0, %1, %2) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// Kept: `add` reads all 64 bits of its operands, and `zextb` changes bits 31:0.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "kept"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %bx = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %0 = "riscv.add"(%zx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %1 = "riscv.addw"(%bx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%0, %1) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      func.func @f0(%[[ADDW_X:.*]]: !riscv.reg, %[[ADDW_Y:.*]]: !riscv.reg) -> !riscv.reg {
// CHECK:      %[[ADDW:.*]] = "riscv.addw"(%[[ADDW_X]], %[[ADDW_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ADDW]]) : (!riscv.reg) -> ()

// CHECK:      func.func @f1(%[[ADDIW_X:.*]]: !riscv.reg) -> !riscv.reg {
// CHECK:      %[[ADDIW:.*]] = "riscv.addiw"(%[[ADDIW_X]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ADDIW]]) : (!riscv.reg) -> ()

// CHECK:      func.func @f2(%[[RORIW_X:.*]]: !riscv.reg) -> !riscv.reg {
// CHECK:      %[[RORIW:.*]] = "riscv.roriw"(%[[RORIW_X]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[RORIW]]) : (!riscv.reg) -> ()

// CHECK:      func.func @f3(%[[SRLIW_X:.*]]: !riscv.reg) -> !riscv.reg {
// CHECK:      %[[SRLIW:.*]] = "riscv.srliw"(%[[SRLIW_X]]) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SRLIW]]) : (!riscv.reg) -> ()

// CHECK:      func.func @f4(%[[SEXTW_X:.*]]: !riscv.reg) -> !riscv.reg {
// CHECK:      %[[SEXTW:.*]] = "riscv.sextw"(%[[SEXTW_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SEXTW]]) : (!riscv.reg) -> ()

// CHECK-LABEL: func.func @binary(
// CHECK-NOT:   "riscv.zextw"

// CHECK-LABEL: func.func @unary(
// CHECK-NOT:   "riscv.zextw"

// CHECK-LABEL: func.func @operands(
// CHECK-NOT:   "riscv.zextw"
// CHECK-NOT:   "riscv.sextw"

// CHECK-LABEL: func.func @kept(
// CHECK:       "riscv.zextw"
// CHECK:       "riscv.zextb"
// CHECK:       "func.return"
