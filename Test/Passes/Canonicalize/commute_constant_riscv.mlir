// RUN: veir-opt %s -p=canonicalize | filecheck %s

// A commutative `riscv` op with the `riscv.li` constant on the left: the
// constant is pushed to the right-hand side.
"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "foo"}> ({
    ^bb0(%x : !riscv.reg):
      // CHECK:      ^{{.*}}(%[[X:.*]] : !riscv.reg):
      %c = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      // CHECK-NEXT: %[[C:.*]] = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
      %add = "riscv.add"(%c, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      // CHECK-NEXT: %[[ADD:.*]] = "riscv.add"(%[[X]], %[[C]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
      "func.return"(%add) : (!riscv.reg) -> ()
      // CHECK-NEXT: "func.return"(%[[ADD]]) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()
