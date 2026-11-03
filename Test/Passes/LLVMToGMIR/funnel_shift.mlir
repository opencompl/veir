// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// Funnel shifts are translated to gMIR, except for `i32` and `i64`, which instruction selection
// still matches in the LLVM dialect.

"builtin.module"() ({
  "func.func"() <{function_type = (i16, i8, i32, i64) -> (), sym_name = "main"}> ({
  ^bb0(%x16: i16, %x8: i8, %x32: i32, %x64: i64):
    %fshl16 = "llvm.intr.fshl"(%x16, %x16, %x16) : (i16, i16, i16) -> i16
    // CHECK:      "gmir.g_fshl"(%{{.*}}, %{{.*}}, %{{.*}}) : (i16, i16, i16) -> i16
    %fshr8 = "llvm.intr.fshr"(%x8, %x8, %x8) : (i8, i8, i8) -> i8
    // CHECK-NEXT: "gmir.g_fshr"(%{{.*}}, %{{.*}}, %{{.*}}) : (i8, i8, i8) -> i8
    %fshl32 = "llvm.intr.fshl"(%x32, %x32, %x32) : (i32, i32, i32) -> i32
    // CHECK-NEXT: "llvm.intr.fshl"(%{{.*}}, %{{.*}}, %{{.*}}) : (i32, i32, i32) -> i32
    %fshr64 = "llvm.intr.fshr"(%x64, %x64, %x64) : (i64, i64, i64) -> i64
    // CHECK-NEXT: "llvm.intr.fshr"(%{{.*}}, %{{.*}}, %{{.*}}) : (i64, i64, i64) -> i64
    "test.test"(%fshl16, %fshr8, %fshl32, %fshr64) : (i16, i8, i32, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
