// RUN: veir-opt %s -p=postlegalizer-combiner-riscv64 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void ()>, sym_name = "main"}> ({
    %x = "test.test"() : () -> i32
    %c = "gmir.g_constant"() <{value = 5 : i32}> : () -> i32
    // `sub_to_add` needs `g_add` and `g_constant` to be legal for the type, which they are not for `i32`.
    // CHECK: "gmir.g_sub"
    %sub = "gmir.g_sub"(%x, %c) : (i32, i32) -> i32
    "test.test"(%sub) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
