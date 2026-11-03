// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i128}> : () -> i128
    %add = "gmir.g_add"(%x, %x) : (i128, i128) -> i128
    "test.test"(%add) : (i128) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Implement narrowing for legalization.
// (This error is expected when a required legalization action has not been
// implemented yet.)
// CHECK: unable to legalize gmir.g_add: no legalization rule matches
