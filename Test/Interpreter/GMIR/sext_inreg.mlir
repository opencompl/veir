// RUN: veir-interpret %s | filecheck %s

// `g_sext_inreg` replaces the bits above the low `sz` bits by copies of bit `sz - 1`.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 6442450944 : i64}> : () -> i64
    %sext_inreg = "gmir.g_sext_inreg"(%x) <{sz = 32 : i64}> : (i64) -> i64
    "llvm.return"(%sext_inreg) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xffffffff80000000#64]
