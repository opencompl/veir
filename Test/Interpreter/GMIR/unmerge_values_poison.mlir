// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    %x = "llvm.mlir.poison"() : () -> i16
    %lo, %hi = "gmir.g_unmerge_values"(%x) : (i16) -> (i8, i8)
    "llvm.return"(%lo) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
