// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

// `llvm.call` and `llvm.return` go through the `riscv` pipeline to LLVM's call
// and return sequences. The `i32` argument is sign-extended (`ADDIW 0`) before
// being passed, as the RISC-V psABI requires.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "ext", function_type = !llvm.func<i64 (i64, i32)>}> ({
  }) : () -> ()
  "llvm.func"() <{sym_name = "caller", function_type = !llvm.func<i64 (i64, i32)>}> ({
  ^bb0(%a: i64, %b: i32):
    %r = "llvm.call"(%a, %b) <{callee = @ext}> : (i64, i32) -> i64
    %s = "llvm.add"(%r, %a) : (i64, i64) -> i64
    "llvm.return"(%s) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:          define i64 @caller(i64 %a0, i64 %a1)
// CHECK:          declare void @ext()
// CHECK-LABEL:  name: caller
// CHECK:          hasCalls: true
// CHECK:          [[A:%arg[0-9_]+]]:gpr = COPY $x10
// CHECK-NEXT:     [[B:%arg[0-9_]+]]:gpr = COPY $x11
// CHECK-NEXT:     [[BEXT:%v[0-9]+]]:gpr = ADDIW [[B]], 0
// CHECK-NEXT:     ADJCALLSTACKDOWN 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:     $x10 = COPY [[A]]
// CHECK-NEXT:     $x11 = COPY [[BEXT]]
// CHECK-NEXT:     PseudoCALL target-flags(riscv-call) @ext, csr_ilp32_lp64, implicit-def dead $x1, implicit $x10, implicit $x11, implicit-def $x2, implicit-def $x10
// CHECK-NEXT:     ADJCALLSTACKUP 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT:     [[R:%v[0-9]+]]:gpr = COPY $x10
// CHECK-NEXT:     [[S:%v[0-9]+]]:gpr = ADD [[R]], [[A]]
// CHECK-NEXT:     $x10 = COPY [[S]]
// CHECK-NEXT:     PseudoRET implicit $x10
// CHECK-NOT:      UNHANDLED
