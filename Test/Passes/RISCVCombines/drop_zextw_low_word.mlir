// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %sum = "riscv.addw"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%sum) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.addiw"(%zx) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.roriw"(%zx) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.srliw"(%zx) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg}> ({
  ^bb0(%x: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %y = "riscv.sextw"(%zx) : (!riscv.reg) -> !riscv.reg
    "func.return"(%y) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      ^{{.*}}(%[[ADDW_X:.*]] : !riscv.reg, %[[ADDW_Y:.*]] : !riscv.reg):
// CHECK:      %[[ADDW:.*]] = "riscv.addw"(%[[ADDW_X]], %[[ADDW_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ADDW]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[ADDIW_X:.*]] : !riscv.reg):
// CHECK:      %[[ADDIW:.*]] = "riscv.addiw"(%[[ADDIW_X]]) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ADDIW]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[RORIW_X:.*]] : !riscv.reg):
// CHECK:      %[[RORIW:.*]] = "riscv.roriw"(%[[RORIW_X]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[RORIW]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[SRLIW_X:.*]] : !riscv.reg):
// CHECK:      %[[SRLIW:.*]] = "riscv.srliw"(%[[SRLIW_X]]) <{"value" = 3 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SRLIW]]) : (!riscv.reg) -> ()

// CHECK:      ^{{.*}}(%[[SEXTW_X:.*]] : !riscv.reg):
// CHECK:      %[[SEXTW:.*]] = "riscv.sextw"(%[[SEXTW_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SEXTW]]) : (!riscv.reg) -> ()
