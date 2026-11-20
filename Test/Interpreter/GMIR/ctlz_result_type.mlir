// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    %a0 = "llvm.mlir.constant"() <{ "value" = 1 : i32 }> : () -> i32
    %x = "gmir.g_ctlz"(%a0) : (i32) -> i8
    "llvm.return"(%x) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x1f#8]
