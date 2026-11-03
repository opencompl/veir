// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    %x = "llvm.mlir.constant"() <{ "value" = 513 : i16 }> : () -> i16
    %lo, %hi = "gmir.g_unmerge_values"(%x) : (i16) -> (i8, i8)
    "llvm.return"(%hi) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x02#8]
