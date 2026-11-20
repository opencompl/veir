// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i128}> : () -> i128
    %mul = "gmir.g_mul"(%x, %x) : (i128, i128) -> i128
    "test.test"(%mul) : (i128) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Implement narrowing and libcalls for legalization.
// CHECK: unable to legalize gmir.g_mul: no legalization rule matches
