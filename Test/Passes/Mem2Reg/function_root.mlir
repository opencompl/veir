// RUN: veir-opt %s --print-op-generic -p=mem2reg | filecheck %s

// The input root can be a function rather than a containing module.
"func.func"() <{sym_name = "root", function_type = (i16) -> i16}> ({
^entry(%a: i16):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i16}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i16, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i16
  "func.return"(%r) : (i16) -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "root"
// CHECK-NEXT: ^{{[^ ]+}}([[ARG:%[^ ]+]] : i16):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: "func.return"([[ARG]]) : (i16) -> ()
// CHECK-NEXT: }) : () -> ()
