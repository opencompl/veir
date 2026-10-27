// RUN: veir-interpret %s | filecheck %s

// A call threads memory through its callee: the caller loads what the callee stores.

"builtin.module"() ({
  "func.func"() <{sym_name = "store42", function_type = (!llvm.ptr) -> ()}> ({
  ^bb0(%p: !llvm.ptr):
    %c42 = "llvm.mlir.constant"() <{value = 42 : i8}> : () -> i8
    "llvm.store"(%c42, %p) : (i8, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %c1 = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%c1) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "func.call"(%p) <{callee = @store42}> : (!llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x2a#8]
