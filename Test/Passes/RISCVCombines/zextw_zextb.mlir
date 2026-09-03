// RUN: veir-opt %s -p=riscv-combine | filecheck %s

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> !riscv.reg, sym_name = "nested_zext"}> ({
  ^bb0(%x : !riscv.reg):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg) -> !riscv.reg
    %zextw = "riscv.zextw"(%zextb) : (!riscv.reg) -> !riscv.reg
    "func.return"(%zextw) : (!riscv.reg) -> ()
  }) : () -> ()

  // The inner result and root use the same fixed register.
  "func.func"() <{function_type = (!riscv.reg<x1>) -> !riscv.reg<x3>, sym_name = "typed_nested_zext"}> ({
  ^bb0(%x : !riscv.reg<x1>):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg<x1>) -> !riscv.reg<x3>
    %zextw = "riscv.zextw"(%zextb) : (!riscv.reg<x3>) -> !riscv.reg<x3>
    "func.return"(%zextw) : (!riscv.reg<x3>) -> ()
  }) : () -> ()

  // Matching register types use forwarding even when the inner op is shared.
  "func.func"() <{function_type = (!riscv.reg<x1>) -> (!riscv.reg<x3>, !riscv.reg<x3>), sym_name = "typed_nested_zext_same_type_shared"}> ({
  ^bb0(%x : !riscv.reg<x1>):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg<x1>) -> !riscv.reg<x3>
    %zextw = "riscv.zextw"(%zextb) : (!riscv.reg<x3>) -> !riscv.reg<x3>
    "func.return"(%zextb, %zextw) : (!riscv.reg<x3>, !riscv.reg<x3>) -> ()
  }) : () -> ()

  // A distinct destination register requires a retargeted zextb.
  "func.func"() <{function_type = (!riscv.reg<x1>) -> !riscv.reg<x3>, sym_name = "typed_nested_zext_distinct"}> ({
  ^bb0(%x : !riscv.reg<x1>):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg<x1>) -> !riscv.reg<x2>
    %zextw = "riscv.zextw"(%zextb) : (!riscv.reg<x2>) -> !riscv.reg<x3>
    "func.return"(%zextw) : (!riscv.reg<x3>) -> ()
  }) : () -> ()

  // Retargeting preserves the original operation when it has another user.
  "func.func"() <{function_type = (!riscv.reg<x1>) -> (!riscv.reg<x2>, !riscv.reg<x3>), sym_name = "typed_nested_zext_shared"}> ({
  ^bb0(%x : !riscv.reg<x1>):
    %zextb = "riscv.zextb"(%x) : (!riscv.reg<x1>) -> !riscv.reg<x2>
    %zextw = "riscv.zextw"(%zextb) : (!riscv.reg<x2>) -> !riscv.reg<x3>
    "func.return"(%zextb, %zextw) : (!riscv.reg<x2>, !riscv.reg<x3>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: "sym_name" = "nested_zext"
// CHECK:      ^{{.*}}(%[[NESTED_X:.*]] : !riscv.reg):
// CHECK-NEXT: %[[NESTED_B:.*]] = "riscv.zextb"(%[[NESTED_X]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[NESTED_B]]) : (!riscv.reg) -> ()

// CHECK-LABEL: "sym_name" = "typed_nested_zext"
// CHECK:      ^{{.*}}(%[[TYPED_NESTED_X:.*]] : !riscv.reg<x1>):
// CHECK-NEXT: %[[TYPED_NESTED_B:.*]] = "riscv.zextb"(%[[TYPED_NESTED_X]]) : (!riscv.reg<x1>) -> !riscv.reg<x3>
// CHECK-NEXT: "func.return"(%[[TYPED_NESTED_B]]) : (!riscv.reg<x3>) -> ()

// CHECK-LABEL: "sym_name" = "typed_nested_zext_same_type_shared"
// CHECK:      ^{{.*}}(%[[TYPED_SAME_X:.*]] : !riscv.reg<x1>):
// CHECK-NEXT: %[[TYPED_SAME_B:.*]] = "riscv.zextb"(%[[TYPED_SAME_X]]) : (!riscv.reg<x1>) -> !riscv.reg<x3>
// CHECK-NEXT: "func.return"(%[[TYPED_SAME_B]], %[[TYPED_SAME_B]]) : (!riscv.reg<x3>, !riscv.reg<x3>) -> ()

// CHECK-LABEL: "sym_name" = "typed_nested_zext_distinct"
// CHECK:      ^{{.*}}(%[[TYPED_DISTINCT_X:.*]] : !riscv.reg<x1>):
// CHECK-NEXT: %[[TYPED_DISTINCT_B:.*]] = "riscv.zextb"(%[[TYPED_DISTINCT_X]]) : (!riscv.reg<x1>) -> !riscv.reg<x3>
// CHECK-NEXT: "func.return"(%[[TYPED_DISTINCT_B]]) : (!riscv.reg<x3>) -> ()

// CHECK-LABEL: "sym_name" = "typed_nested_zext_shared"
// CHECK:      ^{{.*}}(%[[TYPED_SHARED_X:.*]] : !riscv.reg<x1>):
// CHECK-NEXT: %[[TYPED_SHARED_ORIGINAL:.*]] = "riscv.zextb"(%[[TYPED_SHARED_X]]) : (!riscv.reg<x1>) -> !riscv.reg<x2>
// CHECK-NEXT: %[[TYPED_SHARED_RETARGETED:.*]] = "riscv.zextb"(%[[TYPED_SHARED_X]]) : (!riscv.reg<x1>) -> !riscv.reg<x3>
// CHECK-NEXT: "func.return"(%[[TYPED_SHARED_ORIGINAL]], %[[TYPED_SHARED_RETARGETED]]) : (!riscv.reg<x2>, !riscv.reg<x3>) -> ()
