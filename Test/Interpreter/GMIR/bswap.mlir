// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %a0 = "llvm.mlir.constant"() <{ "value" = 305419896 : i32 }> : () -> i32
    %x = "gmir.g_bswap"(%a0) : (i32) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x78563412#32]
