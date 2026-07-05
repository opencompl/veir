// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// A `riscv.zextw` wrapping the result of `and`/`or`/`xor` is redundant when both
// operands are themselves `riscv.zextw`-guarded, since bits 63:32 of the result
// are then guaranteed clear already.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %a = "riscv.and"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %za = "riscv.zextw"(%a) : (!riscv.reg) -> !riscv.reg
    "func.return"(%za) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %o = "riscv.or"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %zo = "riscv.zextw"(%o) : (!riscv.reg) -> !riscv.reg
    "func.return"(%zo) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.xor"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %ze = "riscv.zextw"(%e) : (!riscv.reg) -> !riscv.reg
    "func.return"(%ze) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: only one operand is `zextw`-guarded, so the result's upper
  // bits aren't known clear -- the outer `zextw` must stay.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %e = "riscv.xor"(%zx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %ze = "riscv.zextw"(%e) : (!riscv.reg) -> !riscv.reg
    "func.return"(%ze) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[AND_X:.*]] : !riscv.reg, %[[AND_Y:.*]] : !riscv.reg):
// CHECK:      %[[AND_ZX:.*]] = "riscv.zextw"(%[[AND_X]])
// CHECK:      %[[AND_ZY:.*]] = "riscv.zextw"(%[[AND_Y]])
// CHECK:      %[[AND:.*]] = "riscv.and"(%[[AND_ZX]], %[[AND_ZY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[AND]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[OR_X:.*]] : !riscv.reg, %[[OR_Y:.*]] : !riscv.reg):
// CHECK:      %[[OR_ZX:.*]] = "riscv.zextw"(%[[OR_X]])
// CHECK:      %[[OR_ZY:.*]] = "riscv.zextw"(%[[OR_Y]])
// CHECK:      %[[OR:.*]] = "riscv.or"(%[[OR_ZX]], %[[OR_ZY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[OR]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[XOR_X:.*]] : !riscv.reg, %[[XOR_Y:.*]] : !riscv.reg):
// CHECK:      %[[XOR_ZX:.*]] = "riscv.zextw"(%[[XOR_X]])
// CHECK:      %[[XOR_ZY:.*]] = "riscv.zextw"(%[[XOR_Y]])
// CHECK:      %[[XOR:.*]] = "riscv.xor"(%[[XOR_ZX]], %[[XOR_ZY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[XOR]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[NEG_X:.*]] : !riscv.reg, %[[NEG_Y:.*]] : !riscv.reg):
// CHECK:      %[[NEG_ZX:.*]] = "riscv.zextw"(%[[NEG_X]])
// CHECK:      %[[NEG_XOR:.*]] = "riscv.xor"(%[[NEG_ZX]], %[[NEG_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:      %[[NEG_ZE:.*]] = "riscv.zextw"(%[[NEG_XOR]])
// CHECK-NEXT: "func.return"(%[[NEG_ZE]]) : (!riscv.reg) -> ()
