// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i8) -> (), sym_name = "widen"}> ({
  ^bb0(%p: !llvm.ptr, %x: i8):
    // The value is any-extended, and the store keeps its size.
    // CHECK:      %[[E:.*]] = "gmir.g_anyext"(%{{.*}}) : (i8) -> i64
    // CHECK-NEXT: "gmir.g_store"(%[[E]], %{{.*}}) <{"alignment" = 1 : i64, "size" = 8 : i64}> : (i64, !llvm.ptr) -> ()
    "gmir.g_store"(%x, %p) <{alignment = 1 : i64, size = 8 : i64}> : (i8, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
