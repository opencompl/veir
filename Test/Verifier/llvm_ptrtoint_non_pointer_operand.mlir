// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i64 (i64)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i64):
    %a = "llvm.ptrtoint"(%x) : (i64) -> i64
    "llvm.return"(%a) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.ptrtoint: Expected the pointer side to have !llvm.ptr type
