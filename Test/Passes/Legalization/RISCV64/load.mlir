// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "widen"}> ({
  ^bb0(%p: !llvm.ptr):
    // The result is widened and truncated back, and the load keeps its size.
    // CHECK:      %[[L:.*]] = "gmir.g_load"(%{{.*}}) <{"alignment" = 1 : i64, "size" = 8 : i64}> : (!llvm.ptr) -> i64
    // CHECK-NEXT: %[[T:.*]] = "gmir.g_trunc"(%[[L]]) : (i64) -> i8
    // CHECK-NEXT: "test.test"(%[[T]]) : (i8) -> ()
    %x = "gmir.g_load"(%p) <{alignment = 1 : i64, size = 8 : i64}> : (!llvm.ptr) -> i8
    "test.test"(%x) : (i8) -> ()
    "func.return"() : () -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!llvm.ptr) -> (), sym_name = "legal"}> ({
  ^bb0(%p: !llvm.ptr):
    // Naturally aligned `i64` and pointer results are legal, also when over-aligned.
    // CHECK:      %[[A:.*]] = "gmir.g_load"(%{{.*}}) <{"alignment" = 2 : i64, "size" = 16 : i64}> : (!llvm.ptr) -> i64
    // CHECK-NEXT: %[[B:.*]] = "gmir.g_load"(%{{.*}}) <{"alignment" = 8 : i64, "size" = 32 : i64}> : (!llvm.ptr) -> i64
    // CHECK-NEXT: %[[C:.*]] = "gmir.g_load"(%{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64}> : (!llvm.ptr) -> i64
    // CHECK-NEXT: %[[D:.*]] = "gmir.g_load"(%{{.*}}) <{"alignment" = 8 : i64, "size" = 64 : i64}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK-NEXT: "test.test"(%[[A]], %[[B]], %[[C]], %[[D]])
    %a = "gmir.g_load"(%p) <{alignment = 2 : i64, size = 16 : i64}> : (!llvm.ptr) -> i64
    %b = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 32 : i64}> : (!llvm.ptr) -> i64
    %c = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr) -> i64
    %d = "gmir.g_load"(%p) <{alignment = 8 : i64, size = 64 : i64}> : (!llvm.ptr) -> !llvm.ptr
    "test.test"(%a, %b, %c, %d) : (i64, i64, i64, !llvm.ptr) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
