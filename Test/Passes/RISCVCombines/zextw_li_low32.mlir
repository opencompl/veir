// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.zextw (riscv.li v) -> riscv.li v` when `0 <= v < 2^32`, since `li`'s
// materialized 64-bit value already has bits 63:32 clear in that range.

"builtin.module"() ({
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "foo"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = 16 : i32}> : () -> !riscv.reg
    %z = "riscv.zextw"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: a negative immediate's 64-bit materialization does *not*
  // have bits 63:32 clear (it's sign-extended), so the `zextw` must stay.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "bar"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
    %z = "riscv.zextw"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[C16:.*]] = "riscv.li"() <{"value" = 16 : i32}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[C16]]) : (!riscv.reg) -> ()

// CHECK:      %[[CNEG:.*]] = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
// CHECK-NEXT: %[[Z:.*]] = "riscv.zextw"(%[[CNEG]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[Z]]) : (!riscv.reg) -> ()
