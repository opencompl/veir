// RUN: veir-opt %s --split-input-file --print-op-generic -p=mem2reg | filecheck %s
// RUN: veir-opt %s --split-input-file --print-op-generic -p=mem2reg,mem2reg | filecheck %s

// The last store supplies the value of the load.
// CHECK-LABEL: "sym_name" = "last_store"
// CHECK-NEXT: ^{{[^ ]+}}([[A:%[^ ]+]] : i64, [[B:%[^ ]+]] : i64):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"
// CHECK-NEXT: "func.return"([[B]]) : (i64) -> ()
// CHECK-NEXT: }) : () -> ()
"func.func"() <{sym_name = "last_store", function_type = (i64, i64) -> i64}> ({
^entry(%a: i64, %b: i64):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i64, !llvm.ptr) -> ()
  "llvm.store"(%b, %p) : (i64, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
  "func.return"(%r) : (i64) -> ()
}) : () -> ()

// -----

// Loads before and after a store have different reaching definitions.
// CHECK-LABEL: "sym_name" = "stored_arithmetic"
// CHECK-NEXT: ^{{[^ ]+}}([[A:%[^ ]+]] : i8, [[B:%[^ ]+]] : i8):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"
// CHECK-NEXT: [[SUM:%[^ ]+]] = "arith.addi"([[A]], [[B]]) : (i8, i8) -> i8
// CHECK-NEXT: "func.return"([[SUM]]) : (i8) -> ()
// CHECK-NEXT: }) : () -> ()
"func.func"() <{sym_name = "stored_arithmetic", function_type = (i8, i8) -> i8}> ({
^entry(%a: i8, %b: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %left = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "llvm.store"(%b, %p) : (i8, !llvm.ptr) -> ()
  %right = "llvm.load"(%p) : (!llvm.ptr) -> i8
  %sum = "arith.addi"(%left, %right) : (i8, i8) -> i8
  "llvm.store"(%sum, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// Forwarding a load updates the operand of the following store.
// CHECK-LABEL: "sym_name" = "store_of_load"
// CHECK-NEXT: ^{{[^ ]+}}([[A:%[^ ]+]] : i8):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"
// CHECK-NEXT: "func.return"([[A]]) : (i8) -> ()
// CHECK-NEXT: }) : () -> ()
"func.func"() <{sym_name = "store_of_load", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %first = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "llvm.store"(%first, %p) : (i8, !llvm.ptr) -> ()
  %last = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%last) : (i8) -> ()
}) : () -> ()

// -----

// An unsupported allocation keeps its accesses while the other slot is promoted.
// CHECK-LABEL: "sym_name" = "other_allocation"
// CHECK-NEXT: ^{{[^ ]+}}([[COUNT:%[^ ]+]] : i64, [[A:%[^ ]+]] : i8, [[B:%[^ ]+]] : i8):
// CHECK-NEXT: %{{[^ ]+}} = "arith.constant"
// CHECK-NEXT: [[Q:%[^ ]+]] = "llvm.alloca"([[COUNT]])
// CHECK-NEXT: "llvm.store"([[B]], [[Q]])
// CHECK-NEXT: [[OTHER:%[^ ]+]] = "llvm.load"([[Q]])
// CHECK-NEXT: [[SUM:%[^ ]+]] = "arith.addi"([[A]], [[OTHER]])
// CHECK-NEXT: "llvm.store"([[SUM]], [[Q]])
// CHECK-NEXT: "func.return"([[A]]) : (i8) -> ()
// CHECK-NEXT: }) : () -> ()
"func.func"() <{sym_name = "other_allocation", function_type = (i64, i8, i8) -> i8}> ({
^entry(%count: i64, %a: i8, %b: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %q = "llvm.alloca"(%count) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%b, %q) : (i8, !llvm.ptr) -> ()
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %other = "llvm.load"(%q) : (!llvm.ptr) -> i8
  %first = "llvm.load"(%p) : (!llvm.ptr) -> i8
  %sum = "arith.addi"(%first, %other) : (i8, i8) -> i8
  "llvm.store"(%sum, %q) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()
