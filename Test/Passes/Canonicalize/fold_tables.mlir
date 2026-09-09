// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Each dialect's fold table competes with interpreter evaluation. In
// particular, a table can fire when an operand is not constant at all.
"builtin.module"() ({
  // `arith.addi x, 0` folds to `x` itself: the zero constant is dead
  // afterwards and the addition disappears.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "addi_zero_rhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "addi_zero_rhs"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
      %sum = "arith.addi"(%x, %c0) : (i32, i32) -> i32
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // The fold table only inspects the right operand, since canonical Veir keeps
  // the constant operand of a commutative operation there. With the zero on
  // the left, the commute-constant pattern moves it across first and the fold
  // then fires as above.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "addi_zero_lhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "addi_zero_lhs"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
      %sum = "arith.addi"(%c0, %x) : (i32, i32) -> i32
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // A nonzero addend leaves the operation alone.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "addi_nonzero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "addi_nonzero"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c1 = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
      // CHECK-NEXT: %[[C1:.*]] = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
      %sum = "arith.addi"(%x, %c1) : (i32, i32) -> i32
      // CHECK-NEXT: %[[SUM:.*]] = "arith.addi"(%[[X]], %[[C1]]) : (i32, i32) -> i32
      "func.return"(%sum) : (i32) -> ()
      // CHECK-NEXT: "func.return"(%[[SUM]]) : (i32) -> ()
  }) : () -> ()

  // A table entry decides every result of a multi-result operation:
  // `arith.addui_extended x, 0` is `x` with a false overflow flag, so one
  // result reuses an operand while the other materializes a constant.
  "func.func"() <{function_type = (i32) -> (i32, i1), sym_name = "addui_extended_zero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "addui_extended_zero"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c0 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
      %sum, %overflow = "arith.addui_extended"(%x, %c0) : (i32, i32) -> (i32, i1)
      // CHECK-NEXT: %[[OVERFLOW:.*]] = "arith.constant"() <{"value" = 0 : i1}> : () -> i1
      // CHECK-NEXT: "func.return"(%[[X]], %[[OVERFLOW]]) : (i32, i1) -> ()
      "func.return"(%sum, %overflow) : (i32, i1) -> ()
  }) : () -> ()

  // A nonzero addend leaves the multi-result operation alone.
  "func.func"() <{function_type = (i32) -> (i32, i1), sym_name = "addui_extended_nonzero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "addui_extended_nonzero"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c1 = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
      // CHECK-NEXT: %[[C1:.*]] = "arith.constant"() <{"value" = 1 : i32}> : () -> i32
      %sum, %overflow = "arith.addui_extended"(%x, %c1) : (i32, i32) -> (i32, i1)
      // CHECK-NEXT: %[[R:.*]]:2 = "arith.addui_extended"(%[[X]], %[[C1]]) : (i32, i32) -> (i32, i1)
      "func.return"(%sum, %overflow) : (i32, i1) -> ()
      // CHECK-NEXT: "func.return"(%[[R]]#0, %[[R]]#1) : (i32, i1) -> ()
  }) : () -> ()

  // `riscv.andi x, 0` is zero regardless of `x`. The zero lives in an
  // immediate rather than an operand, so this fold materializes a new
  // constant instead of reusing an operand.
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "andi_zero"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: "sym_name" = "andi_zero"
      %and = "riscv.andi"(%x) <{"value" = 0 : i12}> : (!riscv.reg) -> !riscv.reg
      // CHECK: %[[ZERO:.*]] = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
      // CHECK-NEXT: "func.return"(%[[ZERO]]) : (!riscv.reg) -> ()
      "func.return"(%and) : (!riscv.reg) -> ()
  }) : () -> ()

  // A nonzero immediate with an unknown operand does not fold.
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "andi_nonzero"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK-LABEL: "sym_name" = "andi_nonzero"
      // CHECK:      ^{{.*}}(%[[X:.*]] : !riscv.reg):
      %and = "riscv.andi"(%x) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg
      // CHECK-NEXT: %[[AND:.*]] = "riscv.andi"(%[[X]]) <{"value" = 1 : i12}> : (!riscv.reg) -> !riscv.reg
      "func.return"(%and) : (!riscv.reg) -> ()
      // CHECK-NEXT: "func.return"(%[[AND]]) : (!riscv.reg) -> ()
  }) : () -> ()

  // The same identity fold is table-driven for `llvm.add`. It used to live in
  // instcombine as a rewrite pattern, so it only fires under canonicalize now.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "add_zero_rhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "add_zero_rhs"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c0 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      %sum = "llvm.add"(%x, %c0) : (i32, i32) -> i32
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // With the zero on the left, the commute-constant pattern moves it across
  // first and the fold then fires as above.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "add_zero_lhs"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "add_zero_lhs"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c0 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      %sum = "llvm.add"(%c0, %x) : (i32, i32) -> i32
      // CHECK-NEXT: "func.return"(%[[X]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // A nonzero addend leaves the operation alone.
  "func.func"() <{function_type = (i32) -> i32, sym_name = "add_nonzero"}> ({
    ^bb0(%x : i32):
      // CHECK-LABEL: "sym_name" = "add_nonzero"
      // CHECK:      ^{{.*}}(%[[X:.*]] : i32):
      %c1 = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
      // CHECK-NEXT: %[[C1:.*]] = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
      %sum = "llvm.add"(%x, %c1) : (i32, i32) -> i32
      // CHECK-NEXT: %[[SUM:.*]] = "llvm.add"(%[[X]], %[[C1]]) : (i32, i32) -> i32
      "func.return"(%sum) : (i32) -> ()
      // CHECK-NEXT: "func.return"(%[[SUM]]) : (i32) -> ()
  }) : () -> ()

  // Both the table and the interpreter can fold this operation. The table
  // would reuse the LLVM constant in operand 0, while evaluation produces a
  // concrete constant and therefore wins. The arith spelling of the result
  // makes that choice observable.
  "func.func"() <{function_type = () -> i32, sym_name = "constant_beats_operand"}> ({
    ^bb0():
      // CHECK-LABEL: "sym_name" = "constant_beats_operand"
      %c7 = "llvm.mlir.constant"() <{"value" = 7 : i32}> : () -> i32
      %c0 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      %sum = "arith.addi"(%c7, %c0) : (i32, i32) -> i32
      // CHECK: %[[SEVEN:.*]] = "arith.constant"() <{"value" = 7 : i32}> : () -> i32
      // CHECK-NEXT: "func.return"(%[[SEVEN]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // Here the table would reuse operand 0, but evaluation and poison
  // propagation both produce a poison constant, which has higher preference.
  // Keeping the original poison live makes the fresh folded value observable.
  "func.func"() <{function_type = () -> i32, sym_name = "poison_beats_operand"}> ({
    ^bb0():
      // CHECK-LABEL: "sym_name" = "poison_beats_operand"
      %poison = "llvm.mlir.poison"() : () -> i32
      // CHECK: %[[ORIGINAL:.*]] = "llvm.mlir.poison"() : () -> i32
      %c0 = "llvm.mlir.constant"() <{"value" = 0 : i32}> : () -> i32
      %sum = "llvm.add"(%poison, %c0) : (i32, i32) -> i32
      // CHECK-NEXT: %[[FOLDED:.*]] = "llvm.mlir.poison"() : () -> i32
      "test.test"(%poison) : (i32) -> ()
      // CHECK-NEXT: "test.test"(%[[ORIGINAL]]) : (i32) -> ()
      // CHECK-NEXT: "func.return"(%[[FOLDED]]) : (i32) -> ()
      "func.return"(%sum) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
