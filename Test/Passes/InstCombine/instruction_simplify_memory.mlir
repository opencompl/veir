// RUN: veir-opt %s --print-op-generic -p=instcombine | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "pointer_select", function_type = (i1, !llvm.ptr, !llvm.ptr) -> (!llvm.ptr, !llvm.ptr, !llvm.ptr)}> ({
  ^bb0(%c: i1, %p: !llvm.ptr, %q: !llvm.ptr):
    %true = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %false = "llvm.mlir.constant"() <{value = false}> : () -> i1
    %a = "llvm.select"(%true, %p, %q) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %b = "llvm.select"(%false, %p, %q) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %d = "llvm.select"(%c, %p, %p) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "func.return"(%a, %b, %d) : (!llvm.ptr, !llvm.ptr, !llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "pointer_select"
  // CHECK-NOT: "llvm.select"
  // CHECK: "func.return"(%[[SP:arg[0-9]+_1]], %arg{{[0-9]+}}_2, %[[SP]])

  "func.func"() <{sym_name = "pointer_poison_condition", function_type = (!llvm.ptr, !llvm.ptr) -> !llvm.ptr}> ({
  ^bb0(%p: !llvm.ptr, %q: !llvm.ptr):
    %c = "llvm.mlir.poison"() : () -> i1
    %r = "llvm.select"(%c, %p, %q) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "func.return"(%r) : (!llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "pointer_poison_condition"
  // CHECK: "llvm.mlir.poison"() : () -> !llvm.ptr
  // CHECK-NOT: "llvm.select"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "nested_pointer_select", function_type = (i1, !llvm.ptr, !llvm.ptr, !llvm.ptr) -> (!llvm.ptr, !llvm.ptr)}> ({
  ^bb0(%c: i1, %p: !llvm.ptr, %q: !llvm.ptr, %r: !llvm.ptr):
    %inner = "llvm.select"(%c, %p, %q) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %a = "llvm.select"(%c, %r, %inner) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    %b = "llvm.select"(%c, %inner, %r) : (i1, !llvm.ptr, !llvm.ptr) -> !llvm.ptr
    "func.return"(%a, %b) : (!llvm.ptr, !llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "nested_pointer_select"
  // CHECK: "llvm.select"(%arg{{[0-9]+}}_0, %arg{{[0-9]+}}_3, %arg{{[0-9]+}}_2)
  // CHECK: "llvm.select"(%arg{{[0-9]+}}_0, %arg{{[0-9]+}}_1, %arg{{[0-9]+}}_3)
  // CHECK-NOT: "llvm.select"
  // CHECK: "func.return"

  "func.func"() <{sym_name = "zero_geps", function_type = (!llvm.ptr) -> (!llvm.ptr, !llvm.ptr)}> ({
  ^bb0(%p: !llvm.ptr):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %a = "llvm.getelementptr"(%p) <{rawConstantIndices = array<i32: 0>, elem_type = i8}> : (!llvm.ptr) -> !llvm.ptr
    %b = "llvm.getelementptr"(%p, %zero) <{rawConstantIndices = array<i32: -2147483648>, elem_type = i8}> : (!llvm.ptr, i64) -> !llvm.ptr
    "func.return"(%a, %b) : (!llvm.ptr, !llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "zero_geps"
  // CHECK-NOT: "llvm.getelementptr"
  // CHECK: "func.return"(%[[P:arg[0-9]+_0]], %[[P]])

  "func.func"() <{sym_name = "nonzero_gep", function_type = (!llvm.ptr) -> !llvm.ptr}> ({
  ^bb0(%p: !llvm.ptr):
    %a = "llvm.getelementptr"(%p) <{rawConstantIndices = array<i32: 1>, elem_type = i8}> : (!llvm.ptr) -> !llvm.ptr
    "func.return"(%a) : (!llvm.ptr) -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "nonzero_gep"
  // CHECK: "llvm.getelementptr"

  "func.func"() <{sym_name = "zero_memory", function_type = (!llvm.ptr, !llvm.ptr) -> ()}> ({
  ^bb0(%dst: !llvm.ptr, %src: !llvm.ptr):
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %byte = "llvm.mlir.constant"() <{value = 42 : i8}> : () -> i8
    "llvm.intr.memcpy"(%dst, %src, %zero) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memmove"(%dst, %src, %zero) <{isVolatile = true}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memset"(%dst, %byte, %zero) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memcpy"(%dst, %src, %one) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "func.return"() : () -> ()
  }) : () -> ()
  // CHECK-LABEL: "sym_name" = "zero_memory"
  // CHECK-NOT: "llvm.intr.memmove"
  // CHECK-NOT: "llvm.intr.memset"
  // CHECK: "llvm.intr.memcpy"
  // CHECK-NOT: "llvm.intr.memcpy"
  // CHECK: "func.return"
}) : () -> ()
