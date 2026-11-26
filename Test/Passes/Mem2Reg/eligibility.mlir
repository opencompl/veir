// RUN: veir-opt %s --split-input-file --print-op-generic -p=mem2reg | filecheck %s

// Allocations with more than one element are not promoted.
// CHECK-LABEL: "sym_name" = "multiple_elements"
// CHECK: [[COUNT:%[^ ]+]] = "arith.constant"() <{"value" = 2 : i64}>
// CHECK-NEXT: [[P:%[^ ]+]] = "llvm.alloca"([[COUNT]])
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "multiple_elements", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %two = "arith.constant"() <{value = 2 : i64}> : () -> i64
  %p = "llvm.alloca"(%two) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// The inalloca property prevents promotion.
// CHECK-LABEL: "sym_name" = "inalloca"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"{{.*}}inalloca
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "inalloca", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8, inalloca}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// Volatile stores must be preserved.
// CHECK-LABEL: "sym_name" = "volatile_store"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]]) <{"alignment" = 0 : i64, volatile_}>
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "volatile_store", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) <{volatile_}> : (i8, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// A load before the first store prevents promotion.
// CHECK-LABEL: "sym_name" = "load_before_store"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "load_before_store", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// Stores must match the allocated type.
// CHECK-LABEL: "sym_name" = "mixed_store_type"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"{{.*}}"elem_type" = i8
// CHECK-NEXT: [[WIDE:%[^ ]+]] = "arith.constant"() <{"value" = 3 : i16}>
// CHECK-NEXT: "llvm.store"([[WIDE]], [[P]]) {{.*}} : (i16, !llvm.ptr) -> ()
"func.func"() <{sym_name = "mixed_store_type", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %wide = "arith.constant"() <{value = 3 : i16}> : () -> i16
  "llvm.store"(%wide, %p) : (i16, !llvm.ptr) -> ()
  "func.return"(%a) : (i8) -> ()
}) : () -> ()

// -----

// Loads must match the allocated type.
// CHECK-LABEL: "sym_name" = "mixed_load_type"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"{{.*}}"elem_type" = i8
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: %{{[^ ]+}} = "llvm.load"([[P]]) {{.*}} : (!llvm.ptr) -> i16
"func.func"() <{sym_name = "mixed_load_type", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %wide = "llvm.load"(%p) : (!llvm.ptr) -> i16
  "func.return"(%a) : (i8) -> ()
}) : () -> ()

// -----

// Storing the allocation pointer is an unsupported use.
// CHECK-LABEL: "sym_name" = "stored_pointer"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"{{.*}}"elem_type" = i8
// CHECK-NEXT: [[Q:%[^ ]+]] = "llvm.alloca"{{.*}}"elem_type" = !llvm.ptr
// CHECK-NEXT: "llvm.store"([[P]], [[Q]])
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
"func.func"() <{sym_name = "stored_pointer", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  %q = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
  "llvm.store"(%p, %q) : (!llvm.ptr, !llvm.ptr) -> ()
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "func.return"(%a) : (i8) -> ()
}) : () -> ()

// -----

// Casting the allocation pointer is an unsupported use.
// CHECK-LABEL: "sym_name" = "pointer_cast"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: %{{[^ ]+}} = "llvm.ptrtoint"([[P]])
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "pointer_cast", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  %address = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// Intrinsic calls prevent promotion even without an ordinary call interface.
// CHECK-LABEL: "sym_name" = "intrinsic_call"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: "llvm.call_intrinsic"
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "intrinsic_call", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "llvm.call_intrinsic"() <{intrin = "llvm.donothing", op_bundle_sizes = array<i32>,
    operandSegmentSizes = array<i32: 0, 0>}> : () -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// Blocks containing nested regions are left unchanged.
// CHECK-LABEL: "sym_name" = "nested_region"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: "builtin.module"() ({
// CHECK: "test.test"()
// CHECK: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "nested_region", function_type = (i8) -> i8}> ({
^entry(%a: i8):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i8}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i8, !llvm.ptr) -> ()
  "builtin.module"() ({
    "test.test"() : () -> ()
  }) : () -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i8
  "func.return"(%r) : (i8) -> ()
}) : () -> ()

// -----

// Integer widths outside i8/i16/i32/i64 are not supported.
// CHECK-LABEL: "sym_name" = "unsupported_width"
// CHECK: [[P:%[^ ]+]] = "llvm.alloca"{{.*}}"elem_type" = i128
// CHECK-NEXT: "llvm.store"(%{{[^ ]+}}, [[P]])
// CHECK-NEXT: [[R:%[^ ]+]] = "llvm.load"([[P]])
// CHECK-NEXT: "func.return"([[R]])
"func.func"() <{sym_name = "unsupported_width", function_type = (i128) -> i128}> ({
^entry(%a: i128):
  %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
  %p = "llvm.alloca"(%one) <{elem_type = i128}> : (i64) -> !llvm.ptr
  "llvm.store"(%a, %p) : (i128, !llvm.ptr) -> ()
  %r = "llvm.load"(%p) : (!llvm.ptr) -> i128
  "func.return"(%r) : (i128) -> ()
}) : () -> ()
