// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Byte- and half-word mirrors of the `zextw`/`sextw` bitwise combines: an
// extension wrapping a bitwise op is redundant when the operands already carry
// its high-bit pattern. As with the word versions, `and` under a zero-extension
// needs only one guarded operand; `or`/`xor` and every sign-extension case need
// both.

"builtin.module"() ({
  // zextb + and: one guarded operand suffices.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %a = "riscv.and"(%zx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %za = "riscv.zextb"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"(%za) : (!riscv.reg) -> ()
  }) : () -> ()

  // zexth + or: both operands guarded.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zexth"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zexth"(%y) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.or"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %zo = "riscv.zexth"(%o) : (!riscv.reg) -> !riscv.reg
    "func.return"(%zo) : (!riscv.reg) -> ()
  }) : () -> ()

  // sextb + xor: both operands guarded.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %sx = "riscv.sextb"(%x) : (!riscv.reg) -> !riscv.reg
    %sy = "riscv.sextb"(%y) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.xor"(%sx, %sy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %se = "riscv.sextb"(%e) : (!riscv.reg) -> !riscv.reg
    "func.return"(%se) : (!riscv.reg) -> ()
  }) : () -> ()

  // sexth + and: both operands guarded (sign-extension needs both even for `and`).
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %sx = "riscv.sexth"(%x) : (!riscv.reg) -> !riscv.reg
    %sy = "riscv.sexth"(%y) : (!riscv.reg) -> !riscv.reg
    %a = "riscv.and"(%sx, %sy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sa = "riscv.sexth"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"(%sa) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative: `or` needs both operands guarded -- one `zextb` is not enough.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.or"(%zx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %zo = "riscv.zextb"(%o) : (!riscv.reg) -> !riscv.reg
    "func.return"(%zo) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative: a *sign*-extension needs both operands guarded even for `and`.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %sx = "riscv.sextb"(%x) : (!riscv.reg) -> !riscv.reg
    %a = "riscv.and"(%sx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %sa = "riscv.sextb"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"(%sa) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[A_X:.*]] : !riscv.reg, %[[A_Y:.*]] : !riscv.reg):
// CHECK:      %[[A_ZX:.*]] = "riscv.zextb"(%[[A_X]])
// CHECK:      %[[A_AND:.*]] = "riscv.and"(%[[A_ZX]], %[[A_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[A_AND]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[O_X:.*]] : !riscv.reg, %[[O_Y:.*]] : !riscv.reg):
// CHECK:      %[[O_ZX:.*]] = "riscv.zexth"(%[[O_X]])
// CHECK:      %[[O_ZY:.*]] = "riscv.zexth"(%[[O_Y]])
// CHECK:      %[[O_OR:.*]] = "riscv.or"(%[[O_ZX]], %[[O_ZY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[O_OR]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[E_X:.*]] : !riscv.reg, %[[E_Y:.*]] : !riscv.reg):
// CHECK:      %[[E_SX:.*]] = "riscv.sextb"(%[[E_X]])
// CHECK:      %[[E_SY:.*]] = "riscv.sextb"(%[[E_Y]])
// CHECK:      %[[E_XOR:.*]] = "riscv.xor"(%[[E_SX]], %[[E_SY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[E_XOR]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[H_X:.*]] : !riscv.reg, %[[H_Y:.*]] : !riscv.reg):
// CHECK:      %[[H_SX:.*]] = "riscv.sexth"(%[[H_X]])
// CHECK:      %[[H_SY:.*]] = "riscv.sexth"(%[[H_Y]])
// CHECK:      %[[H_AND:.*]] = "riscv.and"(%[[H_SX]], %[[H_SY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[H_AND]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[NO_X:.*]] : !riscv.reg, %[[NO_Y:.*]] : !riscv.reg):
// CHECK:      %[[NO_ZX:.*]] = "riscv.zextb"(%[[NO_X]])
// CHECK:      %[[NO_OR:.*]] = "riscv.or"(%[[NO_ZX]], %[[NO_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:      %[[NO_ZO:.*]] = "riscv.zextb"(%[[NO_OR]])
// CHECK-NEXT: "func.return"(%[[NO_ZO]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[NA_X:.*]] : !riscv.reg, %[[NA_Y:.*]] : !riscv.reg):
// CHECK:      %[[NA_SX:.*]] = "riscv.sextb"(%[[NA_X]])
// CHECK:      %[[NA_AND:.*]] = "riscv.and"(%[[NA_SX]], %[[NA_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:      %[[NA_SA:.*]] = "riscv.sextb"(%[[NA_AND]])
// CHECK-NEXT: "func.return"(%[[NA_SA]]) : (!riscv.reg) -> ()
