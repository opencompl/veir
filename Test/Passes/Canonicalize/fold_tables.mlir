// RUN: veir-opt %s -p=canonicalize | filecheck %s

// Each dialect's fold table runs ahead of interpreter evaluation, so a fold
// can reuse an existing operand instead of materializing a new constant, and
// can fire even when an operand is not constant at all.
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
}) : () -> ()
