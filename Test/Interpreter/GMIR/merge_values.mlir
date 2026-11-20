// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i16 ()>}> ({
    %lo = "llvm.mlir.constant"() <{ "value" = 1 : i8 }> : () -> i8
    %hi = "llvm.mlir.constant"() <{ "value" = 2 : i8 }> : () -> i8
    %x = "gmir.g_merge_values"(%lo, %hi) : (i8, i8) -> i16
    "llvm.return"(%x) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0201#16]
