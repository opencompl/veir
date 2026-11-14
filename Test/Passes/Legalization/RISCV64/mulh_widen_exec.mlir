// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t.gmir
// RUN: filecheck %s --check-prefix=GMIR < %t.gmir
// RUN: veir-interpret %t.gmir | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// An i13 multiply-high is not legal, and lowers into an i26 multiply shifted
// down by 13, as LLVM's `LegalizerHelper::lowerSMULH_UMULH`; the i26 operations
// are then widened to i64. The signed form extends with the sign and shifts
// arithmetically, the unsigned form zero-extends and shifts logically. The two
// answers differ here, so the lowering cannot have picked the wrong one.

// GMIR: "gmir.g_mul"
// GMIR: "gmir.g_ashr"
// GMIR: "gmir.g_trunc"{{.*}}-> i13
// GMIR: "gmir.g_mul"
// GMIR: "gmir.g_lshr"
// GMIR: "gmir.g_trunc"{{.*}}-> i13
// GMIR-NOT: "gmir.g_smulh"
// GMIR-NOT: "gmir.g_umulh"

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i13, i13)}> ({
    %a_c = "llvm.mlir.constant"() <{value = -4000 : i13}> : () -> i13
    %a = "llvm.freeze"(%a_c) : (i13) -> i13
    %b_c = "llvm.mlir.constant"() <{value = 3 : i13}> : () -> i13
    %b = "llvm.freeze"(%b_c) : (i13) -> i13
    // -4000 * 3 = -12000, whose high 13 bits are -2.
    %s = "llvm.intr.smulh"(%a, %b) : (i13, i13) -> i13
    // The same bits read unsigned are 4192, and 4192 * 3 = 12576 has high 13 bits 1.
    %u = "llvm.intr.umulh"(%a, %b) : (i13, i13) -> i13
    "func.return"(%s, %u) : (i13, i13) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1ffe#13, 0x0001#13]
