// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i32, i64)>
    %v = "llvm.mlir.constant"() <{value = 7 : i32}> : () -> i32
    %r = "llvm.insertvalue"(%u, %v) <{position = array<i64>}> : (!llvm.struct<(i32, i64)>, i32) -> !llvm.struct<(i32, i64)>
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.insertvalue: Expected at least one index in 'position'
