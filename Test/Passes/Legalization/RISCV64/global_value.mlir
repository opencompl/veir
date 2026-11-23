// RUN: not veir-opt --split-input-file %s -p=legalize-riscv64 2>&1 | filecheck %s

// A `g_global_value` is legal only in address space 0.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 1 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
  "func.func"() <{function_type = () -> !llvm.ptr<1>, sym_name = "global_value"}> ({
    %g = "gmir.g_global_value"() <{global_name = @g}> : () -> !llvm.ptr<1>
    "func.return"(%g) : (!llvm.ptr<1>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: unable to legalize gmir.g_global_value: no legalization rule matches

// -----

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 0 : i32}> ({
  }) : () -> ()
  "func.func"() <{function_type = () -> !llvm.ptr, sym_name = "global_value"}> ({
    // CHECK-LABEL: func.func @global_value
    // CHECK:       %[[G:.*]] = "gmir.g_global_value"() <{"global_name" = @g}> : () -> !llvm.ptr
    // CHECK-NEXT:  "func.return"(%[[G]])
    %g = "gmir.g_global_value"() <{global_name = @g}> : () -> !llvm.ptr
    "func.return"(%g) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()
