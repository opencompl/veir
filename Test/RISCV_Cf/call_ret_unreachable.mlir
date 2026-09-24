// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  ^4():
    "func.func"() <{function_type = (!riscv.reg, i1) -> !riscv.reg, sym_name = "foo"}> ({
      ^6(%a : !riscv.reg, %c : i1):
        %r = "riscv_cf.call"(%a, %a) <{"callee" = @g}> : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "riscv_cf.call"() <{"callee" = @h}> : () -> ()
        %cr = "builtin.unrealized_conversion_cast"(%c) : (i1) -> !riscv.reg
        "riscv_cf.bnez"(%cr) [^7, ^8] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
      ^7():
        "riscv_cf.ret"(%r) : (!riscv.reg) -> ()
      ^8():
        "riscv_cf.unreachable"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      "riscv_cf.call"(%{{.*}}, %{{.*}}) <{"callee" = @g}> : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "riscv_cf.call"() <{"callee" = @h}> : () -> ()
// CHECK:      "riscv_cf.ret"(%{{.*}}) : (!riscv.reg) -> ()
// CHECK:      "riscv_cf.unreachable"() : () -> ()
