// RUN: veir-opt %s | filecheck %s
// RUN: MLIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i2 (i32, i32)>, linkage = #llvm.linkage<external>, sym_name = "f", visibility_ = 0 : i64}> ({
  ^bb0(%a: i32, %b: i32):
    %s = "llvm.intr.scmp"(%a, %b) : (i32, i32) -> i2
    %u = "llvm.intr.ucmp"(%a, %b) : (i32, i32) -> i8
    %w = "llvm.intr.scmp"(%a, %b) : (i32, i32) -> i64
    "llvm.return"(%s) : (i2) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "llvm.intr.scmp"(%{{.*}}, %{{.*}}) : (i32, i32) -> i2
// CHECK: "llvm.intr.ucmp"(%{{.*}}, %{{.*}}) : (i32, i32) -> i8
// CHECK: "llvm.intr.scmp"(%{{.*}}, %{{.*}}) : (i32, i32) -> i64
