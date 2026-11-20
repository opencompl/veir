// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i32, i64)>
    %r = "llvm.extractvalue"(%u) <{position = array<i64: 2>}> : (!llvm.struct<(i32, i64)>) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.extractvalue: position out of bounds: 2
