// RUN: not veir-opt %s -p=legalize-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zext = "gmir.g_zext"(%x) : (i64) -> i128
    "test.test"(%zext) : (i128) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// Extensions to more than 64 bits are unsupported until narrowing is implemented.
// CHECK: unable to legalize gmir.g_zext: no legalization rule matches
