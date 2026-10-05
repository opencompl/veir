// RUN: not veir-opt %s --disable-verifiers -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %ptr = "llvm.mlir.zero"() : () -> !llvm.ptr
    %add = "gmir.g_add"(%ptr, %ptr) : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "test.test"(%add) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: unable to legalize gmir.g_add: unsupported type !llvm.ptr
