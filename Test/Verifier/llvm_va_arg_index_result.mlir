// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (!llvm.ptr)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %r = "llvm.va_arg"(%p) : (!llvm.ptr) -> index
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: llvm.va_arg: result 0 must be an LLVM dialect-compatible type, but got index
