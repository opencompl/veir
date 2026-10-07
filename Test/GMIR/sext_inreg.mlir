// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %x = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %sext_inreg = "gmir.g_sext_inreg"(%x) <{sz = 32 : i64}> : (i64) -> i64
    "test.test"(%sext_inreg) : (i64) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: "gmir.g_sext_inreg"(%{{.*}}) <{"sz" = 32 : i64}> : (i64) -> i64
