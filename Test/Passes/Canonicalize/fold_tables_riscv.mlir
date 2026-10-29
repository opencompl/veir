// RUN: veir-opt %s -p=canonicalize | filecheck %s

// A sample of the `riscv` fold table, whose entries apply when only some
// operands are known. `Riscv.tryFold_sound` proves every entry; these check
// that each kind of fold reaches the IR: reusing an operand, materializing a
// constant, a select-like `czero`, and an entry that must not fire.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "andi_ones"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: func.func @andi_ones(
      // CHECK-SAME: %[[X:[^:]*]]: !riscv.reg)
      // CHECK-NOT: "riscv.andi"
      // CHECK: "func.return"(%[[X]])
      %r = "riscv.andi"(%x) <{"value" = -1 : i64}> : (!riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "mv"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: func.func @mv(
      // CHECK-SAME: %[[X:[^:]*]]: !riscv.reg)
      // CHECK-NOT: "riscv.mv"
      // CHECK: "func.return"(%[[X]])
      %r = "riscv.mv"(%x) : (!riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "or_ones"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: func.func @or_ones(
      // CHECK-SAME: %[[X:[^:]*]]: !riscv.reg)
      // CHECK-NOT: "riscv.or"
      // CHECK: %[[R:.*]] = "riscv.li"() <{"value" = -1 : i64}>
      // CHECK-NOT: "riscv.or"
      // CHECK: "func.return"(%[[R]])
      %c1 = "riscv.li"() <{"value" = -1 : i64}> : () -> !riscv.reg
      %r = "riscv.or"(%x, %c1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "div_zero"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: func.func @div_zero(
      // CHECK-SAME: %[[X:[^:]*]]: !riscv.reg)
      // CHECK-NOT: "riscv.div"
      // CHECK: %[[R:.*]] = "riscv.li"() <{"value" = -1 : i64}>
      // CHECK-NOT: "riscv.div"
      // CHECK: "func.return"(%[[R]])
      %c1 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      %r = "riscv.div"(%x, %c1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "czeroeqz_nonzero_cond"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: func.func @czeroeqz_nonzero_cond(
      // CHECK-SAME: %[[X:[^:]*]]: !riscv.reg)
      // CHECK-NOT: "riscv.czeroeqz"
      // CHECK: "func.return"(%[[X]])
      %c1 = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      %r = "riscv.czeroeqz"(%x, %c1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "czeronez_nonzero_cond"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: func.func @czeronez_nonzero_cond(
      // CHECK-SAME: %[[X:[^:]*]]: !riscv.reg)
      // CHECK-NOT: "riscv.czeronez"
      // CHECK: %[[R:.*]] = "riscv.li"() <{"value" = 0 : i64}>
      // CHECK-NOT: "riscv.czeronez"
      // CHECK: "func.return"(%[[R]])
      %c1 = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      %r = "riscv.czeronez"(%x, %c1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "remw_zero"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: func.func @remw_zero(
      // CHECK-SAME: %[[X:[^:]*]]: !riscv.reg)
      // CHECK: "riscv.remw"
      %c1 = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      %r = "riscv.remw"(%x, %c1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()
