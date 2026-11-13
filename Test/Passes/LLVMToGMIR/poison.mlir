// RUN: veir-opt %s -p=llvm-to-gmir | filecheck %s

// An integer or pointer `llvm.mlir.poison` becomes `g_poison`. A byte one becomes `g_poison` on
// the integer of the same width.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "poison", function_type = !llvm.func<void ()>}> ({
    // CHECK-DAG:  "gmir.g_poison"() : () -> i32
    // CHECK-DAG:  "gmir.g_poison"() : () -> !llvm.ptr
    // CHECK-DAG:  %[[B:.*]] = "gmir.g_poison"() : () -> i16
    // CHECK-DAG:  "gmir.g_trunc"(%[[B]]) : (i16) -> i8
    // CHECK-NOT:  llvm.mlir.poison
    %x = "llvm.mlir.poison"() : () -> i32
    %p = "llvm.mlir.poison"() : () -> !llvm.ptr
    %b = "llvm.mlir.poison"() : () -> !llvm.byte<16>
    %t = "llvm.trunc"(%b) : (!llvm.byte<16>) -> !llvm.byte<8>
    "test.test"(%x, %p, %t) : (i32, !llvm.ptr, !llvm.byte<8>) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
