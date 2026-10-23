// RUN: veir-interpret %s | filecheck %s --check-prefix=EXEC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=EXEC
// RUN: filecheck %s --input-file=%t

// Sign extensions from widths other than 8, 16 and 32 become `g_sext_inreg`, which is selected
// as a shift left and an arithmetic shift right. `reconcile-cast` also
// zero-extends the narrow constants first, with `slli` + `srli` (and a `zextw` for `i32`).
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i32)}> ({
    %neg = "llvm.mlir.constant"() <{value = 64 : i7}> : () -> i7
    %pos = "llvm.mlir.constant"() <{value = 63 : i7}> : () -> i7
    %true = "llvm.mlir.constant"() <{value = 1 : i1}> : () -> i1
    // CHECK:      "riscv.srli"
    // CHECK:      %[[X:.*]] = "riscv.slli"({{.*}}) <{"value" = 57 : i64}>
    // CHECK-NEXT: "riscv.srai"(%[[X]]) <{"value" = 57 : i64}>
    %a = "llvm.sext"(%neg) : (i7) -> i64
    // CHECK:      "riscv.srli"
    // CHECK:      %[[X:.*]] = "riscv.slli"({{.*}}) <{"value" = 57 : i64}>
    // CHECK-NEXT: "riscv.srai"(%[[X]]) <{"value" = 57 : i64}>
    %b = "llvm.sext"(%pos) : (i7) -> i64
    // CHECK:      "riscv.srli"
    // CHECK:      %[[X:.*]] = "riscv.slli"({{.*}}) <{"value" = 63 : i64}>
    // CHECK-NEXT: "riscv.srai"(%[[X]]) <{"value" = 63 : i64}>
    %c = "llvm.sext"(%true) : (i1) -> i64
    // CHECK:      "riscv.srli"
    // CHECK:      %[[X:.*]] = "riscv.slli"({{.*}}) <{"value" = 57 : i64}>
    // CHECK-NEXT: "riscv.srai"(%[[X]]) <{"value" = 57 : i64}>
    %d = "llvm.sext"(%neg) : (i7) -> i32
    "func.return"(%a, %b, %c, %d) : (i64, i64, i64, i32) -> ()
  }) : () -> ()
}) : () -> ()

// EXEC: Program output: #[0xffffffffffffffc0#64, 0x000000000000003f#64, 0xffffffffffffffff#64, 0xffffffc0#32]
