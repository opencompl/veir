// RUN: veir-opt %s --print-op-generic -p=mem2reg | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=mem2reg,mem2reg | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "external", function_type = () -> i32}> ({}) : () -> ()

  // Both slots are removed. Promoting p changes the value stored into q.
  "func.func"() <{sym_name = "two_slots", function_type = (i32, i32) -> i32}> ({
  ^entry(%a: i32, %b: i32):
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    %first = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "llvm.store"(%first, %q) : (i32, !llvm.ptr) -> ()
    %last = "llvm.load"(%q) : (!llvm.ptr) -> i32
    %sum = "arith.addi"(%last, %b) : (i32, i32) -> i32
    "func.return"(%sum) : (i32) -> ()
  }) : () -> ()

  // A second function is visited independently.
  "func.func"() <{sym_name = "second", function_type = (i8) -> i8}> ({
  ^entry(%a: i8):
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
    "func.return"(%r) : (i8) -> ()
  }) : () -> ()

  // The second count becomes constant only after the first slot is promoted.
  "func.func"() <{sym_name = "count_from_slot", function_type = (i32) -> i32}> ({
  ^entry(%a: i32):
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %count_slot = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%one, %count_slot) : (i64, !llvm.ptr) -> ()
    %count = "llvm.load"(%count_slot) : (!llvm.ptr) -> i64
    %p = "llvm.alloca"(%count) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.store"(%a, %p) : (i32, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "func.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "func.func"() <{"function_type" = () -> i32, "sym_name" = "external"}> ({}) : () -> ()
// CHECK-LABEL: "sym_name" = "two_slots"
// CHECK-NEXT: ^{{[^ ]+}}([[A:%[^ ]+]] : i32, [[B:%[^ ]+]] : i32):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: [[SUM:%[^ ]+]] = "arith.addi"([[A]], [[B]]) : (i32, i32) -> i32
// CHECK-NEXT: "func.return"([[SUM]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-LABEL: "sym_name" = "second"
// CHECK-NEXT: ^{{[^ ]+}}([[ARG:%[^ ]+]] : i8):
// CHECK-NEXT: %{{[^ ]+}} = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: "func.return"([[ARG]]) : (i8) -> ()
// CHECK-NEXT: }) : () -> ()
// CHECK-LABEL: "sym_name" = "count_from_slot"
// CHECK-NEXT: ^{{[^ ]+}}([[VALUE:%[^ ]+]] : i32):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: "func.return"([[VALUE]]) : (i32) -> ()
// CHECK-NEXT: }) : () -> ()
