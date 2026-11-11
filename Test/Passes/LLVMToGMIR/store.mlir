// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void (ptr, i8, i32, i64, ptr, i24)>}> ({
  ^bb0(%p: !llvm.ptr, %a: i8, %b: i32, %c: i64, %d: !llvm.ptr, %e: i24):
    // Naturally aligned stores become `g_store`, whose `size` is in bits and `alignment` in bytes.
    // CHECK:      "gmir.g_store"(%{{.*}}, %{{.*}}) <{"alignment" = 1 : i64, "size" = 8 : i64}> : (i8, !llvm.ptr) -> ()
    // CHECK-NEXT: "gmir.g_store"(%{{.*}}, %{{.*}}) <{"alignment" = 8 : i64, "size" = 32 : i64}> : (i32, !llvm.ptr) -> ()
    // CHECK-NEXT: "gmir.g_store"(%{{.*}}, %{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64}> : (i64, !llvm.ptr) -> ()
    // CHECK-NEXT: "gmir.g_store"(%{{.*}}, %{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%a, %p) <{alignment = 1 : i64}> : (i8, !llvm.ptr) -> ()
    "llvm.store"(%b, %p) <{alignment = 8 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%c, %p) <{alignment = 8 : i64}> : (i64, !llvm.ptr) -> ()
    "llvm.store"(%d, %p) <{alignment = 8 : i64}> : (!llvm.ptr, !llvm.ptr) -> ()
    // The access flags are kept.
    // CHECK-NEXT: "gmir.g_store"(%{{.*}}, %{{.*}}) <{"alignment" = 4 : i64, "size" = 32 : i64, volatile_}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%b, %p) <{alignment = 4 : i64, volatile_}> : (i32, !llvm.ptr) -> ()
    // Misaligned and odd-sized stores stay in the LLVM dialect.
    // CHECK-NEXT: "llvm.store"(%{{.*}}, %{{.*}}) <{"alignment" = 2 : i64}> : (i32, !llvm.ptr) -> ()
    // CHECK-NEXT: "llvm.store"(%{{.*}}, %{{.*}}) <{"alignment" = 4 : i64}> : (i24, !llvm.ptr) -> ()
    "llvm.store"(%b, %p) <{alignment = 2 : i64}> : (i32, !llvm.ptr) -> ()
    "llvm.store"(%e, %p) <{alignment = 4 : i64}> : (i24, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
