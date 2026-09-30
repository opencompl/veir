// RUN: veir2mir %s | filecheck %s

// `riscv_cf.call` and `riscv_cf.return` lower to LLVM's call and return
// sequences, with arguments in a0-a7 and results in a0-a1. Every function with
// a body gets its own MIR document; direct callees defined nowhere in the
// module are declared in the stub IR so the MIR parser can resolve them.

"builtin.module"() ({
  "func.func"() <{sym_name = "caller", function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg)}> ({
  ^entry(%target: !riscv.reg, %arg: !riscv.reg):
    %one = "riscv_cf.call"(%arg) <{callee = @external}> : (!riscv.reg) -> !riscv.reg
    %first, %second = "riscv_cf.call"(%target, %one, %arg) : (!riscv.reg, !riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg)
    "riscv_cf.call"() <{callee = @leaf}> : () -> ()
    "riscv_cf.return"(%first, %second) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "leaf", function_type = !llvm.func<void ()>}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "too_many_args", function_type = (!riscv.reg) -> ()}> ({
  ^entry(%a: !riscv.reg):
    "riscv_cf.call"(%a, %a, %a, %a, %a, %a, %a, %a, %a) <{callee = @external}> : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// The stub IR defines each function with a body, and declares `external` but
// not the locally defined `leaf`.
// CHECK:          define i64 @caller(i64 %a0, i64 %a1)
// CHECK:          define i64 @leaf()
// CHECK:          define i64 @too_many_args(i64 %a0)
// CHECK-NOT:      declare void @leaf
// CHECK:          declare void @external()
// CHECK-NOT:      declare

// A function that calls must say so, or the machine verifier rejects its
// ADJCALLSTACK pseudos and `ra` is not saved.
// CHECK-LABEL:  name: caller
// CHECK:        frameInfo:
// CHECK-NEXT:     adjustsStack: true
// CHECK-NEXT:     hasCalls: true
// CHECK:          [[TARGET:%arg[0-9_]+]]:gpr = COPY $x10
// CHECK-NEXT:     [[ARG:%arg[0-9_]+]]:gpr = COPY $x11

// Direct call with one argument and one result.
// CHECK-NEXT:     ADJCALLSTACKDOWN 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:     $x10 = COPY [[ARG]]
// CHECK-NEXT:     PseudoCALL @external, csr_ilp32_lp64, implicit-def dead $x1, implicit $x10, implicit-def $x2, implicit-def $x10
// CHECK-NEXT:     ADJCALLSTACKUP 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:     [[ONE:%v[0-9]+]]:gpr = COPY $x10

// Indirect call: the target moves to the class `PseudoCALLIndirect` needs, and
// the remaining operands are the arguments. Two results come back in a0/a1.
// CHECK-NEXT:     [[T:%t[0-9]+]]:gprjalrnonx7 = COPY [[TARGET]]
// CHECK-NEXT:     ADJCALLSTACKDOWN 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:     $x10 = COPY [[ONE]]
// CHECK-NEXT:     $x11 = COPY [[ARG]]
// CHECK-NEXT:     PseudoCALLIndirect [[T]], csr_ilp32_lp64, implicit-def dead $x1, implicit $x10, implicit $x11, implicit-def $x2, implicit-def $x10, implicit-def $x11
// CHECK-NEXT:     ADJCALLSTACKUP 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:     [[FIRST:%v[0-9]+]]:gpr = COPY $x10
// CHECK-NEXT:     [[SECOND:%v[0-9]+_1]]:gpr = COPY $x11

// A call with neither arguments nor results.
// CHECK-NEXT:     ADJCALLSTACKDOWN 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:     PseudoCALL @leaf, csr_ilp32_lp64, implicit-def dead $x1, implicit-def $x2
// CHECK-NEXT:     ADJCALLSTACKUP 0, 0, implicit-def dead $x2, implicit $x2

// CHECK-NEXT:     $x10 = COPY [[FIRST]]
// CHECK-NEXT:     $x11 = COPY [[SECOND]]
// CHECK-NEXT:     PseudoRET implicit $x10, implicit $x11

// A leaf function needs no frameInfo; a void return returns nothing.
// CHECK-LABEL:  name: leaf
// CHECK-NOT:      frameInfo:
// CHECK:          bb.0:
// CHECK-NEXT:     PseudoRET{{$}}

// Stack-passed arguments are not lowered.
// CHECK-LABEL:  name: too_many_args
// CHECK:          ; UNHANDLED riscv_cf.call with 9 args and 0 results
