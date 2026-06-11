// RUN: VEIR_ROUNDTRIP

"builtin.module"() ({
  "llvm.func"() <{sym_name = "with_fixed", function_type = !llvm.func<i32 (ptr, ...)>}> ({}) : () -> ()
  "llvm.func"() <{sym_name = "only_varargs", function_type = !llvm.func<i32 (...)>}> ({}) : () -> ()
}) : () -> ()

// CHECK: "llvm.func"() <{"function_type" = !llvm.func<i32 (!llvm.ptr, ...)>, "sym_name" = "with_fixed"}> ({{.*}}) : () -> ()
// CHECK: "llvm.func"() <{"function_type" = !llvm.func<i32 (...)>, "sym_name" = "only_varargs"}> ({{.*}}) : () -> ()
