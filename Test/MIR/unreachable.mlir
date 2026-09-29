// RUN: veir2mir %s | filecheck %s

// A `main` lowered to the riscv / riscv_cf dialects whose block ^9 ends in
// `riscv_cf.unreachable`, which becomes a trapping UNIMP with no successors.
// Produced from `llvm.unreachable` by `veir-opt -p=riscv`.

"builtin.module"() ({
  ^4():
    "llvm.func"() <{"function_type" = !llvm.func<!riscv.reg (!riscv.reg)>, "sym_name" = "main"}> ({
      ^6(%arg6_0 : !riscv.reg):
        %23 = "riscv.sltiu"(%arg6_0) <{"value" = 1 : i64}> : (!riscv.reg) -> !riscv.reg
        "riscv_cf.bnez"(%23, %arg6_0) [^9, ^10] <{"operandSegmentSizes" = array<i32: 1, 0, 1>}> : (!riscv.reg, !riscv.reg) -> ()
      ^9():
        "riscv_cf.unreachable"() : () -> ()
      ^10(%arg10_0 : !riscv.reg):
        "llvm.return"(%arg10_0) : (!riscv.reg) -> ()
    }) : () -> ()
}) : () -> ()

// CHECK:      bb.0:
// CHECK-NEXT:   successors: %bb.1, %bb.2
// CHECK:        BNE %v{{[0-9]+}}, $x0, %bb.1
// CHECK-NEXT:   PseudoBR %bb.2
// CHECK:      bb.1:
// CHECK-NEXT:   UNIMP
// CHECK-EMPTY:
// CHECK-NEXT: bb.2:
// CHECK:        PseudoRET implicit $x10
