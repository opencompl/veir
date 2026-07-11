// RUN: veir-opt %s -p=canonicalize,dce | filecheck %s

// Folding of RISC-V register arithmetic.
"builtin.module"() ({
  // All-constant operations are evaluated and replaced by a `riscv.li`.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "fold_add"}> ({
      %c7 = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
      %c8 = "riscv.li"() <{"value" = 8 : i64}> : () -> !riscv.reg
      %sum = "riscv.add"(%c7, %c8) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      // CHECK:      %[[C15:.*]] = "riscv.li"() <{"value" = 15 : i64}> : () -> !riscv.reg
      // CHECK-NEXT: "func.return"(%[[C15]]) : (!riscv.reg) -> ()
      "func.return"(%sum) : (!riscv.reg) -> ()
  }) : () -> ()

  // add(x, 0) -> x
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "add_zero"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK:      ^{{.*}}(%[[X:.*]] : !riscv.reg):
      // CHECK-NEXT: "func.return"(%[[X]]) : (!riscv.reg) -> ()
      %c0 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      %r = "riscv.add"(%x, %c0) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  // and(x, 0) -> 0, for any x
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "and_zero"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK:      %[[C0:.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      // CHECK-NEXT: "func.return"(%[[C0]]) : (!riscv.reg) -> ()
      %c0 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      %r = "riscv.and"(%x, %c0) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  // addi(x) with immediate 0 -> x: an identity that folds on the
  // operation's properties rather than on a constant operand.
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "addi_zero"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK:      ^{{.*}}(%[[Y:.*]] : !riscv.reg):
      // CHECK-NEXT: "func.return"(%[[Y]]) : (!riscv.reg) -> ()
      %r = "riscv.addi"(%x) <{"value" = 0 : i12}> : (!riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  // Chained evaluation through an immediate operation: addi(li 41) with
  // immediate 1 evaluates to li 42.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "fold_addi"}> ({
      %c41 = "riscv.li"() <{"value" = 41 : i64}> : () -> !riscv.reg
      %r = "riscv.addi"(%c41) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg
      // CHECK:      %[[C42:.*]] = "riscv.li"() <{"value" = 42 : i64}> : () -> !riscv.reg
      // CHECK-NEXT: "func.return"(%[[C42]]) : (!riscv.reg) -> ()
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: "riscv.add"
// CHECK-NOT: "riscv.and"
// CHECK-NOT: "riscv.addi"
