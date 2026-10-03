// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// As in LLVM, a pointer only bitcasts to a pointer; crossing between pointers
// and integers is `llvm.inttoptr` and `llvm.ptrtoint`.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %p = "llvm.mlir.zero"() : () -> !llvm.ptr
    %a = "llvm.bitcast"(%p) : (!llvm.ptr) -> i64
    "func.return"(%a) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.bitcast: Expected a pointer to bitcast to a pointer
