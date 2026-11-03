// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// `llvm.mlir.undef` takes nothing: it is a source of value, not a cast.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<i32 (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i32):
    %u = "llvm.mlir.undef"(%x) : (i32) -> i32
    "llvm.return"(%u) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.mlir.undef: Expected 0 operand(s)
