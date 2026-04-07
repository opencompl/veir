


// ──────────────────────────────────────────────────────────────────────────────
// Invalid: i32 operands – lowering must NOT fire (guard: bitwidth ≠ 64)
// The llvm.icmp should survive unchanged for every predicate.
// ──────────────────────────────────────────────────────────────────────────────

// CHECK-LABEL: "func.func"() <{"sym_name" = "icmp_eq_i32_no_lower"
"builtin.module"() ({
  "func.func"() <{"sym_name" = "icmp_eq_i32_no_lower", "function_type" = () -> ()}> ({
    %a = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
    %r = "llvm.icmp"(%a, %b) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 0 : i64}> : (i32, i32) -> i1
    // CHECK-NOT:  "riscv.xor"
    // CHECK-NOT:  "riscv.sltiu"
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "func.func"() <{"sym_name" = "icmp_slt_i32_no_lower"
"builtin.module"() ({
  "func.func"() <{"sym_name" = "icmp_slt_i32_no_lower", "function_type" = () -> ()}> ({
    %a = "llvm.mlir.constant"() <{"value" = 1 : i32}> : () -> i32
    %b = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
    %r = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i32, i32) -> i1
    // CHECK-NOT:  "riscv.slt"
  }) : () -> ()
}) : () -> ()

// Invalid: mixed widths – lhs i64, rhs i32.
// The rhs guard (bitwidth ≠ 64) trips before any ops are emitted.

// CHECK-LABEL: "func.func"() <{"sym_name" = "icmp_slt_mixed_no_lower"
"builtin.module"() ({
  "func.func"() <{"sym_name" = "icmp_slt_mixed_no_lower", "function_type" = () -> ()}> ({
    %a = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{"value" = 2 : i32}> : () -> i32
    %r = "llvm.icmp"(%a, %b) <{"predicate" = 2 : i64}> : (i64, i32) -> i1
    // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i64, i32) -> i1
    // CHECK-NOT:  "riscv.slt"
  }) : () -> ()
}) : () -> ()

// Invalid: unknown predicate (≥ 10) – the wildcard arm returns the rewriter
// unchanged, so the llvm.icmp survives.

// CHECK-LABEL: "func.func"() <{"sym_name" = "icmp_unknown_predicate_no_lower"
"builtin.module"() ({
  "func.func"() <{"sym_name" = "icmp_unknown_predicate_no_lower", "function_type" = () -> ()}> ({
    %a = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
    %b = "llvm.mlir.constant"() <{"value" = 2 : i64}> : () -> i64
    %r = "llvm.icmp"(%a, %b) <{"predicate" = 99 : i64}> : (i64, i64) -> i1
    // CHECK:      "llvm.icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 99 : i64}> : (i64, i64) -> i1
    // CHECK-NOT:  "riscv.
  }) : () -> ()
}) : () -> ()s