// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %a0 = "llvm.mlir.constant"() <{ "value" = 6 : i32 }> : () -> i32
    %a1 = "llvm.mlir.constant"() <{ "value" = 7 : i32 }> : () -> i32
    %x = "gmir.g_mul"(%a0, %a1) : (i32, i32) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000002a#32]
