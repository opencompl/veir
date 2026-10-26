// RUN: veir-opt %s -p=dce | filecheck %s

// Allocation changes observable final memory even when its result is unused.
// Retaining it also keeps its size operand alive through the greedy driver.

"builtin.module"() ({
  "func.func"() <{function_type = () -> (), sym_name = "llvm_alloc"}> ({
    %one = "arith.constant"() <{value = 1 : i64}> : () -> i64
    %unused = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "func.return"() : () -> ()
  }) : () -> ()
  "func.func"() <{function_type = () -> (), sym_name = "riscv_alloc"}> ({
    %unused = "riscv_stack.alloca"() <{size = 8 : i64, alignment = 8 : i64}> : () -> !riscv.reg
    "func.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-LABEL: func.func @llvm_alloc() {
// CHECK-NEXT: %[[ONE:.*]] = "arith.constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: %{{.*}} = "llvm.alloca"(%[[ONE]]) <{"alignment" = 0 : i64, "elem_type" = i64}> : (i64) -> !llvm.ptr
// CHECK-NEXT: "func.return"() : () -> ()
// CHECK-LABEL: func.func @riscv_alloc() {
// CHECK-NEXT: %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"() : () -> ()
