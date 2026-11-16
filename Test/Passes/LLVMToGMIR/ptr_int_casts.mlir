// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// Casts between a pointer and an `i64` become `g_ptrtoint`/`g_inttoptr`; other widths stay.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "casts", function_type = !llvm.func<void (ptr, i64)>}> ({
  ^bb0(%p : !llvm.ptr, %x : i64):
    // CHECK:      "gmir.g_ptrtoint"(%{{.*}}) : (!llvm.ptr) -> i64
    // CHECK-NEXT: "gmir.g_inttoptr"(%{{.*}}) : (i64) -> !llvm.ptr
    // CHECK-NEXT: "llvm.ptrtoint"(%{{.*}}) : (!llvm.ptr) -> i32
    %i = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    %q = "llvm.inttoptr"(%x) : (i64) -> !llvm.ptr
    %j = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i32
    "test.test"(%i, %q, %j) : (i64, !llvm.ptr, i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
