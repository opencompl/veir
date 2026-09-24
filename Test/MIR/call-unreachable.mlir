// RUN: veir2mir %s | filecheck %s

// Calls, returns and unreachable, as lowered by `-p=riscv`:
//   * each callee is declared in the stub IR module, and the frame is marked
//     as making calls,
//   * `riscv_cf.call` becomes the sequence LLVM's own selector emits, with the
//     arguments in a0-a7 and the result copied out of a0,
//   * `riscv_cf.ret` returns in a0, and `riscv_cf.unreachable` traps.

"builtin.module"() ({
  ^4():
    "llvm.func"() <{"function_type" = !llvm.func<!riscv.reg (!riscv.reg, i1)>, "sym_name" = "main"}> ({
      ^6(%arg6_0 : !riscv.reg, %arg6_1 : i1):
        %25 = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
        %19 = "riscv_cf.call"(%arg6_0, %25) <{"callee" = @g}> : (!riscv.reg, !riscv.reg) -> !riscv.reg
        "riscv_cf.call"() <{"callee" = @h}> : () -> ()
        %22 = "builtin.unrealized_conversion_cast"(%arg6_1) : (i1) -> !riscv.reg
        "riscv_cf.bnez"(%22) [^10, ^11] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
      ^10():
        "riscv_cf.ret"(%19) : (!riscv.reg) -> ()
      ^11():
        "riscv_cf.unreachable"() : () -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      declare void @g()
// CHECK-NEXT: declare void @h()
// CHECK:      frameInfo:
// CHECK-NEXT:   adjustsStack:    true
// CHECK-NEXT:   hasCalls:        true
// CHECK:      bb.0:
// CHECK:        [[K:%v[0-9]+]]:gpr = PseudoLI 7
// CHECK-NEXT:   ADJCALLSTACKDOWN 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:   $x10 = COPY %arg6_0
// CHECK-NEXT:   $x11 = COPY [[K]]
// CHECK-NEXT:   PseudoCALL target-flags(riscv-call) @g, csr_ilp32_lp64, implicit-def dead $x1, implicit $x10, implicit $x11, implicit-def $x2, implicit-def $x10
// CHECK-NEXT:   ADJCALLSTACKUP 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:   [[R:%v[0-9]+]]:gpr = COPY $x10
// CHECK-NEXT:   ADJCALLSTACKDOWN 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:   PseudoCALL target-flags(riscv-call) @h, csr_ilp32_lp64, implicit-def dead $x1, implicit-def $x2
// CHECK-NEXT:   ADJCALLSTACKUP 0, 0, implicit-def dead $x2, implicit $x2
// CHECK:      bb.1:
// CHECK-NEXT:   $x10 = COPY [[R]]
// CHECK-NEXT:   PseudoRET implicit $x10
// CHECK:      bb.2:
// CHECK-NEXT:   UNIMP
