// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void (ptr)>}> ({
  ^bb0(%p: !llvm.ptr):
    // Naturally aligned loads become `g_load`, whose `size` is in bits and `alignment` in bytes.
    // CHECK:      "gmir.g_load"(%{{.*}}) <{"alignment" = 1 : i64, "size" = 8 : i64}> : (!llvm.ptr) -> i8
    // CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 2 : i64, "size" = 16 : i64}> : (!llvm.ptr) -> i16
    // CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 8 : i64, "size" = 32 : i64}> : (!llvm.ptr) -> i32
    // CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64}> : (!llvm.ptr) -> i64
    // CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64}> : (!llvm.ptr) -> !llvm.ptr
    %a = "llvm.load"(%p) <{alignment = 1 : i64}> : (!llvm.ptr) -> i8
    %b = "llvm.load"(%p) <{alignment = 2 : i64}> : (!llvm.ptr) -> i16
    %c = "llvm.load"(%p) <{alignment = 8 : i64}> : (!llvm.ptr) -> i32
    %d = "llvm.load"(%p) <{alignment = 8 : i64}> : (!llvm.ptr) -> i64
    %e = "llvm.load"(%p) <{alignment = 8 : i64}> : (!llvm.ptr) -> !llvm.ptr
    // A missing alignment is the natural one, and the access flags are kept.
    // CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 4 : i64, "size" = 32 : i64}> : (!llvm.ptr) -> i32
    // CHECK-NEXT: "gmir.g_load"(%{{.*}}) <{"alignment" = 4 : i64, "size" = 32 : i64, volatile_}> : (!llvm.ptr) -> i32
    %f = "llvm.load"(%p) : (!llvm.ptr) -> i32
    %g = "llvm.load"(%p) <{alignment = 4 : i64, volatile_}> : (!llvm.ptr) -> i32
    // Misaligned, odd-sized and byte loads stay in the LLVM dialect.
    // CHECK-NEXT: "llvm.load"(%{{.*}}) <{"alignment" = 2 : i64}> : (!llvm.ptr) -> i32
    // CHECK-NEXT: "llvm.load"(%{{.*}}) <{"alignment" = 4 : i64}> : (!llvm.ptr) -> i24
    // CHECK-NEXT: "llvm.load"(%{{.*}}) <{"alignment" = 1 : i64}> : (!llvm.ptr) -> !llvm.byte<8>
    %h = "llvm.load"(%p) <{alignment = 2 : i64}> : (!llvm.ptr) -> i32
    %i = "llvm.load"(%p) <{alignment = 4 : i64}> : (!llvm.ptr) -> i24
    %j = "llvm.load"(%p) <{alignment = 1 : i64}> : (!llvm.ptr) -> !llvm.byte<8>
    "test.test"(%a, %b, %c, %d, %e, %f, %g, %h, %i, %j) : (i8, i16, i32, i64, !llvm.ptr, i32, i32, i32, i24, !llvm.byte<8>) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
