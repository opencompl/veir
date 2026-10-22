// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "gmir.g_constant"() <{value = 1 : i128}> : () -> i128
    "test.test"(%x) : (i128) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// TODO: Implement narrowing for legalization.
// CHECK: unable to legalize gmir.g_constant: no legalization rule matches
