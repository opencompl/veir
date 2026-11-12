// RUN: veir-opt %s -p=llvm-to-gmir,legalize-riscv64,dce | filecheck %s --check-prefix=LEGAL
// RUN: veir-opt %s -p=riscv > %t && filecheck %s --check-prefix=ISEL --input-file=%t
// RUN: filecheck %s --check-prefix=CLEAN --input-file=%t

// CLEAN: "builtin.module"
// CLEAN-NOT: "gmir
// CLEAN-NOT: "llvm.intr.

// LLVM's GlobalISel lowerThreewayCompare emits zext(gt) - zext(lt). RISC-V uses
// two slt/sltu instructions and sub, or subw for an i32 result. The arguments
// are unknown so constant folding cannot hide a missing legalization rule.

"builtin.module"() ({
  "func.func"() <{sym_name = "signed64", function_type = (i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64):
    // LEGAL-LABEL: func.func @signed64
    // LEGAL: %[[GT:.*]] = "gmir.g_icmp"(%[[A:.*]], %[[B:.*]]) <{"predicate" = 4 : i64}> : (i64, i64) -> i64
    // LEGAL-NEXT: %[[LT:.*]] = "gmir.g_icmp"(%[[A]], %[[B]]) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
    // LEGAL-NEXT: %[[R:.*]] = "gmir.g_sub"(%[[GT]], %[[LT]]) : (i64, i64) -> i64
    // LEGAL-NEXT: "func.return"(%[[R]]) : (i64) -> ()
    // ISEL-LABEL: func.func @signed64
    // ISEL: %[[GT:.*]] = "riscv.slt"(%{{.*}}, %{{.*}})
    // ISEL: %[[LT:.*]] = "riscv.slt"(%{{.*}}, %{{.*}})
    // ISEL-NEXT: "riscv.sub"(%[[GT]], %[[LT]])
    %r = "llvm.intr.scmp"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "unsigned64", function_type = (i64, i64) -> i64}> ({
  ^bb0(%a: i64, %b: i64):
    // LEGAL-LABEL: func.func @unsigned64
    // LEGAL: %[[GT:.*]] = "gmir.g_icmp"(%[[A:.*]], %[[B:.*]]) <{"predicate" = 8 : i64}> : (i64, i64) -> i64
    // LEGAL-NEXT: %[[LT:.*]] = "gmir.g_icmp"(%[[A]], %[[B]]) <{"predicate" = 6 : i64}> : (i64, i64) -> i64
    // LEGAL-NEXT: %[[R:.*]] = "gmir.g_sub"(%[[GT]], %[[LT]]) : (i64, i64) -> i64
    // LEGAL-NEXT: "func.return"(%[[R]]) : (i64) -> ()
    // ISEL-LABEL: func.func @unsigned64
    // ISEL: %[[GT:.*]] = "riscv.sltu"(%{{.*}}, %{{.*}})
    // ISEL: %[[LT:.*]] = "riscv.sltu"(%{{.*}}, %{{.*}})
    // ISEL-NEXT: "riscv.sub"(%[[GT]], %[[LT]])
    %r = "llvm.intr.ucmp"(%a, %b) : (i64, i64) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()

  // Widen the operands independently of the result; use the word subtraction.
  "func.func"() <{sym_name = "signed8_to_32", function_type = (i8, i8) -> i32}> ({
  ^bb0(%a: i8, %b: i8):
    // LEGAL-LABEL: func.func @signed8_to_32
    // LEGAL: "gmir.g_sext_inreg"(%{{.*}}) <{"sz" = 8 : i64}>
    // LEGAL: "gmir.g_icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 4 : i64}>
    // LEGAL: "gmir.g_icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}>
    // LEGAL: %[[R:.*]] = "gmir_riscv.g_subw"(%{{.*}}, %{{.*}})
    // LEGAL-NEXT: "gmir.g_trunc"(%[[R]]) : (i64) -> i32
    // ISEL-LABEL: func.func @signed8_to_32
    // ISEL: "riscv.sextb"
    // ISEL: %[[GT:.*]] = "riscv.slt"(%{{.*}}, %{{.*}})
    // ISEL: %[[LT:.*]] = "riscv.slt"(%{{.*}}, %{{.*}})
    // ISEL-NEXT: "riscv.subw"(%[[GT]], %[[LT]])
    %r = "llvm.intr.scmp"(%a, %b) : (i8, i8) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  // An i2 result still holds -1, 0, and 1 after truncating the subtraction.
  "func.func"() <{sym_name = "unsigned64_to_2", function_type = (i64, i64) -> i2}> ({
  ^bb0(%a: i64, %b: i64):
    // LEGAL-LABEL: func.func @unsigned64_to_2
    // LEGAL: "gmir.g_icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 8 : i64}>
    // LEGAL: "gmir.g_icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 6 : i64}>
    // LEGAL: %[[R:.*]] = "gmir.g_sub"(%{{.*}}, %{{.*}})
    // LEGAL-NEXT: "gmir.g_trunc"(%[[R]]) : (i64) -> i2
    // ISEL-LABEL: func.func @unsigned64_to_2
    // ISEL: %[[GT:.*]] = "riscv.sltu"(%{{.*}}, %{{.*}})
    // ISEL: %[[LT:.*]] = "riscv.sltu"(%{{.*}}, %{{.*}})
    // ISEL-NEXT: "riscv.sub"(%[[GT]], %[[LT]])
    %r = "llvm.intr.ucmp"(%a, %b) : (i64, i64) -> i2
    "func.return"(%r) : (i2) -> ()
  }) : () -> ()
}) : () -> ()
