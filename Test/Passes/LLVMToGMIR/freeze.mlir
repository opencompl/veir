// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// An integer `llvm.freeze` becomes `g_freeze`; a pointer one stays in the LLVM dialect.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "freeze", function_type = !llvm.func<void (i32, ptr)>}> ({
  ^bb0(%x : i32, %p : !llvm.ptr):
    // CHECK:      "gmir.g_freeze"(%{{.*}}) : (i32) -> i32
    // CHECK-NEXT: "llvm.freeze"(%{{.*}}) : (!llvm.ptr) -> !llvm.ptr
    %fx = "llvm.freeze"(%x) : (i32) -> i32
    %fp = "llvm.freeze"(%p) : (!llvm.ptr) -> !llvm.ptr
    "test.test"(%fx, %fp) : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
