// RUN: veir-opt %s --print-op-generic -p=mem2reg | filecheck %s

"builtin.module"() ({
  // An unsupported allocation must not prevent promotion of its neighbour.
  "func.func"() <{sym_name = "mixed", function_type = (i64, i32) -> i32}> ({
  ^entry(%count: i64, %a: i32):
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %dynamic = "llvm.alloca"(%count) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %dynamic) : (i32, !llvm.ptr) -> ()
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
    %unused = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "volatile", function_type = (i32) -> i32}> ({
  ^entry(%a: i32):
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) <{volatile_}> : (!llvm.ptr) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "cfg", function_type = (i32) -> i32}> ({
  ^entry(%a: i32):
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    "cf.br"() [^exit] : () -> ()
  ^exit:
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()

  "func.func"() <{sym_name = "callee", function_type = () -> i32}> ({}) : () -> ()

  "func.func"() <{sym_name = "calls", function_type = (i32) -> i32}> ({
  ^entry(%a: i32):
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    %ignored = "func.call"() <{callee = @callee}> : () -> i32
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "mixed"
// CHECK-NEXT: ^{{[^ ]+}}([[COUNT:%[^ ]+]] : i64, [[A:%[^ ]+]] : i32):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: [[DYNAMIC:%[^ ]+]] = "llvm.alloca"([[COUNT]])
// CHECK-NEXT: "llvm.store"([[A]], [[DYNAMIC]]) <{"alignment" = 0 : i64}> : (i32, !llvm.ptr) -> ()
// CHECK-NEXT: %{{[^ ]+}} = "llvm.alloca"
// CHECK-NEXT: "func.return"([[A]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-LABEL: "sym_name" = "volatile"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]]) <{"alignment" = 0 : i64, volatile_}>
// CHECK-NEXT: "func.return"([[R]]) : (i32) -> ()
// CHECK-LABEL: "sym_name" = "cfg"
// CHECK: [[SLOT:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[SLOT]])
// CHECK-NEXT: "cf.br"() [^[[EXIT:[0-9]+]]] : () -> ()
// CHECK-NEXT: ^[[EXIT]]():
// CHECK-NEXT: [[VALUE:%[^ ]+]] = "llvm.load"([[SLOT]])
// CHECK-NEXT: "func.return"([[VALUE]]) : (i32) -> ()
// CHECK-LABEL: "sym_name" = "calls"
// CHECK: [[CALL_SLOT:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[CALL_SLOT]])
// CHECK-NEXT: %{{[^ ]+}} = "func.call"() <{"callee" = @callee}> : () -> i32
// CHECK-NEXT: [[CALL_VALUE:%[^ ]+]] = "llvm.load"([[CALL_SLOT]])
// CHECK-NEXT: "func.return"([[CALL_VALUE]]) : (i32) -> ()
