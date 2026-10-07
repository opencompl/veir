// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x_i8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %x_i64 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %x_i128 = "llvm.mlir.constant"() <{value = 1 : i128}> : () -> i128
    %add = "gmir.g_add"(%x_i64, %x_i64) <{overflowFlags = 3 : i32}> : (i64, i64) -> i64
    // CHECK:      "gmir.g_add"({{.*}}) <{"overflowFlags" = 3 : i32}> : (i64, i64) -> i64
    %cmp = "gmir.g_icmp"(%x_i64, %x_i64) <{predicate = 0 : i64}> : (i64, i64) -> i64
    // CHECK-NEXT: "gmir.g_icmp"({{.*}}) <{"predicate" = 0 : i64}> : (i64, i64) -> i64
    %sext = "gmir.g_sext"(%x_i8) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_sext"({{.*}}) : (i8) -> i64
    %trunc = "gmir.g_trunc"(%x_i128) : (i128) -> i8
    // CHECK-NEXT: "gmir.g_trunc"({{.*}}) : (i128) -> i8
    %sext_inreg = "gmir.g_sext_inreg"(%x_i64) <{sz = 32 : i64}> : (i64) -> i64
    // CHECK-NEXT: "gmir.g_sext_inreg"({{.*}}) <{"sz" = 32 : i64}> : (i64) -> i64
    %llvm_add = "llvm.add"(%x_i8, %x_i8) : (i8, i8) -> i8
    // Non gMIR instructions are all legal for now!
    // CHECK-NEXT: "llvm.add"({{.*}}) : (i8, i8) -> i8
    "test.test"(%add, %cmp, %sext, %trunc, %sext_inreg, %llvm_add) : (i64, i64, i64, i8, i64, i8) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
