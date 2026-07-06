// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A `riscv.sextw` wrapping the result of `and`/`or`/`xor` is redundant when both
// operands are themselves `riscv.sextw`-guarded: bitwise ops act bit-by-bit, so
// if each operand's bits 63:32 already equal its bit 31, so do the result's.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %sx = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    %sy = "riscv.sextw"(%y) : (!riscv.reg) -> !riscv.reg
    %a = "riscv.and"(%sx, %sy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sa = "riscv.sextw"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"(%sa) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %sx = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    %sy = "riscv.sextw"(%y) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.or"(%sx, %sy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %so = "riscv.sextw"(%o) : (!riscv.reg) -> !riscv.reg
    "func.return"(%so) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %sx = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    %sy = "riscv.sextw"(%y) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.xor"(%sx, %sy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %se = "riscv.sextw"(%e) : (!riscv.reg) -> !riscv.reg
    "func.return"(%se) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: only one operand is `sextw`-guarded, so the result's upper
  // bits aren't known to match bit 31 -- the outer `sextw` must stay.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %sx = "riscv.sextw"(%x) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.xor"(%sx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %se = "riscv.sextw"(%e) : (!riscv.reg) -> !riscv.reg
    "func.return"(%se) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[AND_X:.*]] : !riscv.reg, %[[AND_Y:.*]] : !riscv.reg):
// CHECK:      %[[AND_SX:.*]] = "riscv.sextw"(%[[AND_X]])
// CHECK:      %[[AND_SY:.*]] = "riscv.sextw"(%[[AND_Y]])
// CHECK:      %[[AND:.*]] = "riscv.and"(%[[AND_SX]], %[[AND_SY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[AND]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[OR_X:.*]] : !riscv.reg, %[[OR_Y:.*]] : !riscv.reg):
// CHECK:      %[[OR_SX:.*]] = "riscv.sextw"(%[[OR_X]])
// CHECK:      %[[OR_SY:.*]] = "riscv.sextw"(%[[OR_Y]])
// CHECK:      %[[OR:.*]] = "riscv.or"(%[[OR_SX]], %[[OR_SY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[OR]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[XOR_X:.*]] : !riscv.reg, %[[XOR_Y:.*]] : !riscv.reg):
// CHECK:      %[[XOR_SX:.*]] = "riscv.sextw"(%[[XOR_X]])
// CHECK:      %[[XOR_SY:.*]] = "riscv.sextw"(%[[XOR_Y]])
// CHECK:      %[[XOR:.*]] = "riscv.xor"(%[[XOR_SX]], %[[XOR_SY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[XOR]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[NEG_X:.*]] : !riscv.reg, %[[NEG_Y:.*]] : !riscv.reg):
// CHECK:      %[[NEG_SX:.*]] = "riscv.sextw"(%[[NEG_X]])
// CHECK:      %[[NEG_XOR:.*]] = "riscv.xor"(%[[NEG_SX]], %[[NEG_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:      %[[NEG_SE:.*]] = "riscv.sextw"(%[[NEG_XOR]])
// CHECK-NEXT: "func.return"(%[[NEG_SE]]) : (!riscv.reg) -> ()
