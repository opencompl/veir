// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// `llvm.mlir.addressof` becomes `g_global_value`.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{sym_name = "addressof", function_type = !llvm.func<!llvm.ptr ()>}> ({
  ^bb0():
    // CHECK: "gmir.g_global_value"() <{"global_name" = @g}> : () -> !llvm.ptr
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%g) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()
