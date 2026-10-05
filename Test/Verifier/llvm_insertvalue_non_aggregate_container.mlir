// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32, i64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%i: i32, %l: i64):
    %u = "llvm.mlir.undef"() : () -> !llvm.struct<(i32, i64)>
    %a = "llvm.mlir.undef"() : () -> !llvm.array<2 x i32>
    %r = "llvm.insertvalue"(%i, %i) <{position = array<i64: 0>}> : (i32, i32) -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.insertvalue: Expected an aggregate container, but got i32
