// RUN: veir-opt %s -p=dce | filecheck %s

// An unused `g_load` can be removed unless it is volatile, and a `g_store`
// always remains.
// This test confirms this behavior: We leave a plain load, a volatile load and
// a store unused and ensure that DCE removes only the plain load.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %plain = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr) -> i64
    %volatile = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64, volatile_}> : (!llvm.ptr) -> i64
    "gmir.g_store"(%one, %p) <{alignment = 8 : i64, size = 64 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.alloca"
// CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64, volatile_}> : (!llvm.ptr) -> i64
// CHECK-NEXT: "gmir.g_store"(%{{.*}}, %{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64}> : (i64, !llvm.ptr) -> ()
// CHECK-NEXT: "llvm.return"() : () -> ()
