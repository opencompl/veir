// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%i: i32):
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i32, i64)>
    %a = "llvm.mlir.undef"() : () -> !llvm.array<2 x i32>
    %r = "llvm.extractvalue"(%a) <{position = array<i64: 0>}> : (!llvm.array<2 x i32>) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.extractvalue: Type mismatch: extracting from !llvm.array<2 x i32> should produce i32 but this op returns i64
