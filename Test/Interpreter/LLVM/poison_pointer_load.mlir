// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC

// Loading from a poison pointer is undefined behaviour.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %v = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
