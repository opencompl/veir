// RUN: veir-interpret %s | filecheck %s

// Loading from a poison pointer is undefined behaviour.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %v = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
