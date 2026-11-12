// RUN: not veir-opt %s --disable-verifiers -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %ptr = "llvm.mlir.zero"() : () -> !llvm.ptr
    %add = "gmir.g_add"(%ptr, %ptr) : (!llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "test.test"(%add) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// The pass checks that its input verifies before it legalizes anything, so an addition of
// pointers is rejected by the verifier.
// CHECK: legalize-riscv64: the module does not verify: gmir.g_add: Expected operand 0 to have integer type
