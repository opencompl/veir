// RUN: veir-opt %s --split-input-file --print-op-generic -p=mem2reg | filecheck %s

// Use the function interface when the root is an LLVM function.
// CHECK-LABEL: "sym_name" = "root"
// CHECK-NEXT: ^{{[^ ]+}}([[ARG:%[^ ]+]] : i32):
// CHECK-NEXT: %{{[^ ]+}} = "llvm.mlir.constant"
// CHECK-NEXT: "llvm.return"([[ARG]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
"llvm.func"() <{sym_name = "root", function_type = !llvm.func<i32 (i32)>}> ({
^entry(%a: i32):
  %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
  "llvm.return"(%r) : (i32) -> ()
}) : () -> ()

// -----

// Collect LLVM functions inside a module and skip declarations.
// CHECK-LABEL: "sym_name" = "external"
// CHECK-SAME: ({}) : () -> ()
// CHECK-LABEL: "sym_name" = "nested"
// CHECK-NEXT: ^{{[^ ]+}}([[ARG:%[^ ]+]] : i32):
// CHECK-NEXT: %{{[^ ]+}} = "llvm.mlir.constant"
// CHECK-NEXT: "llvm.return"([[ARG]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
"builtin.module"() ({
  "llvm.func"() <{sym_name = "external", function_type = !llvm.func<i32 ()>}> ({}) : () -> ()

  "llvm.func"() <{sym_name = "nested", function_type = !llvm.func<i32 (i32)>}> ({
  ^entry(%a: i32):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()
