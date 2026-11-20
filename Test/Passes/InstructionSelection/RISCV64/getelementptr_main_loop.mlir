// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// The main loop lowers each `llvm.getelementptr` with the instance of `getelementptr_pattern` its
// decomposition selects (`getelementptrRules`): here `p + i`, at stride 1 and no constant offset,
// next to the `gmir.g_add` selected as usual.

// CHECK:      %[[P:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
// CHECK-NEXT: %[[I:.*]] = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
// CHECK-NEXT: %[[A:.*]] = "riscv.add"(%[[P]], %[[I]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK-NEXT: "builtin.unrealized_conversion_cast"(%[[A]]) : (!riscv.reg) -> !llvm.ptr
// CHECK: "riscv.add"

"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i64, i64) -> (!llvm.ptr, i64), sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %i: i64, %j: i64):
    %gep = "llvm.getelementptr"(%p, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %add = "gmir.g_add"(%i, %j) : (i64, i64) -> i64
    "func.return"(%gep, %add) : (!llvm.ptr, i64) -> ()
  }) : () -> ()
}) : () -> ()
