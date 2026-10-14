// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a0 = "llvm.mlir.constant"() <{ "value" = 255 : i64 }> : () -> i64
    %x = "gmir.g_sext_inreg"(%a0) <{ sz = 8 : i64 }> : (i64) -> i64
    "llvm.return"(%x) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffffffffffff#64]
