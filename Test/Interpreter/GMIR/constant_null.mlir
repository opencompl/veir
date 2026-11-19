// RUN: veir-interpret %s | filecheck %s

// A pointer `g_constant` is the pointer with that address.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<!llvm.ptr ()>}> ({
    %p = "gmir.g_constant"() <{value = 0 : i64}> : () -> !llvm.ptr
    "llvm.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[ptr(0)]
