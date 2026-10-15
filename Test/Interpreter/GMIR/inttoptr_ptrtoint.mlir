// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %a = "llvm.mlir.constant"() <{ "value" = 4096 : i64 }> : () -> i64
    %p = "gmir.g_inttoptr"(%a) : (i64) -> !llvm.ptr
    %x = "gmir.g_ptrtoint"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%x) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000001000#64]
