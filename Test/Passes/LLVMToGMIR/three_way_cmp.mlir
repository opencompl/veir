// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// Three-way comparisons become `g_scmp`/`g_ucmp`, keeping the result width. Operands or results
// wider than 64 bits stay in the LLVM dialect.

"builtin.module"() ({
  "func.func"() <{function_type = (i32, i64, i128) -> (), sym_name = "main"}> ({
  ^bb0(%x: i32, %y: i64, %z: i128):
    %scmp = "llvm.intr.scmp"(%x, %x) : (i32, i32) -> i8
    // CHECK:      "gmir.g_scmp"(%{{.*}}, %{{.*}}) : (i32, i32) -> i8
    %ucmp = "llvm.intr.ucmp"(%y, %y) : (i64, i64) -> i2
    // CHECK-NEXT: "gmir.g_ucmp"(%{{.*}}, %{{.*}}) : (i64, i64) -> i2
    %scmp_wide_result = "llvm.intr.scmp"(%x, %x) : (i32, i32) -> i128
    // CHECK-NEXT: "llvm.intr.scmp"(%{{.*}}, %{{.*}}) : (i32, i32) -> i128
    %ucmp_wide_operands = "llvm.intr.ucmp"(%z, %z) : (i128, i128) -> i8
    // CHECK-NEXT: "llvm.intr.ucmp"(%{{.*}}, %{{.*}}) : (i128, i128) -> i8
    "test.test"(%scmp, %ucmp, %scmp_wide_result, %ucmp_wide_operands) : (i8, i2, i128, i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
