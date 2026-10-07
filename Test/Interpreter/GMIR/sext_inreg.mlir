// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64)}> ({
    %c127 = "llvm.mlir.constant"() <{ "value" = 127 : i64 }> : () -> i64
    %c255 = "llvm.mlir.constant"() <{ "value" = 255 : i64 }> : () -> i64
    %a = "gmir.g_sext_inreg"(%c127) <{ sz = 8 : i64 }> : (i64) -> i64
    %b = "gmir.g_sext_inreg"(%c255) <{ sz = 8 : i64 }> : (i64) -> i64
    "func.return"(%a, %b) : (i64, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000007f#64, 0xffffffffffffffff#64]
