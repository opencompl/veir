// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    %x = "gmir.g_constant"() <{ "value" = -1 : i8 }> : () -> i8
    "llvm.return"(%x) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xff#8]
