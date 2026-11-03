// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i32, struct<(i64, i8)>)>
    %r = "llvm.extractvalue"(%u) <{position = array<i64: 1, 1>}> : (!llvm.struct<(i32, struct<(i64, i8)>)>) -> i64
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.extractvalue: Type mismatch: extracting from !llvm.struct<(i32, !llvm.struct<(i64, i8)>)> should produce i8 but this op returns i64
