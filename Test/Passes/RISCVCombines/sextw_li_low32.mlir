// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// `riscv.sextw (riscv.li v) -> riscv.li v` when `-2^31 <= v < 2^31`, since in
// that signed range `li`'s materialized 64-bit value already equals the sign-
// extension of its own low 32 bits. Note this includes negative immediates,
// unlike the unsigned range of `zextw_li_low32`.

"builtin.module"() ({
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "foo"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = 16 : i32}> : () -> !riscv.reg
    %s = "riscv.sextw"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s) : (!riscv.reg) -> ()
  }) : () -> ()

  // A negative immediate is fine here: -1 is already sign-extended, so `sextw`
  // is redundant (this is where the sext range differs from the zext one).
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "bar"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
    %s = "riscv.sextw"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%s) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[C16:.*]] = "riscv.li"() <{"value" = 16 : i32}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[C16]]) : (!riscv.reg) -> ()

// CHECK:      %[[CNEG:.*]] = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[CNEG]]) : (!riscv.reg) -> ()
