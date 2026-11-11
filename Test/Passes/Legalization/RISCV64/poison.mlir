// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s

// A narrow `g_poison` is widened to `i64` and truncated back; a pointer one is legal.

"builtin.module"() ({
  "func.func"() <{function_type = () -> i8, sym_name = "poison"}> ({
    // CHECK-LABEL: func.func @poison
    // CHECK:       %[[W:.*]] = "gmir.g_poison"() : () -> i64
    // CHECK-NEXT:  %[[T:.*]] = "gmir.g_trunc"(%[[W]]) : (i64) -> i8
    // CHECK-NEXT:  "func.return"(%[[T]])
    %x = "gmir.g_poison"() : () -> i8
    "func.return"(%x) : (i8) -> ()
  }) : () -> ()
  "func.func"() <{function_type = () -> !llvm.ptr, sym_name = "poison_ptr"}> ({
    // CHECK-LABEL: func.func @poison_ptr
    // CHECK:       %[[P:.*]] = "gmir.g_poison"() : () -> !llvm.ptr
    // CHECK-NEXT:  "func.return"(%[[P]])
    %p = "gmir.g_poison"() : () -> !llvm.ptr
    "func.return"(%p) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()
