// RUN: veir-opt %s -p=isel-riscv64{strict} | filecheck %s
// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s --check-prefix=LAX

// The strict pass only runs the selections proved to refine the module. The
// `getelementptr` lowering is not one of them, so it is left unselected, while
// the `gmir.g_add` next to it is selected as usual.

// CHECK: "llvm.getelementptr"
// CHECK: "riscv.add"
// LAX-NOT: "llvm.getelementptr"
// LAX: "riscv.add"

"builtin.module"() ({
  "func.func"() <{function_type = (!llvm.ptr, i64, i64) -> (!llvm.ptr, i64), sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr, %i: i64, %j: i64):
    %gep = "llvm.getelementptr"(%p, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %add = "gmir.g_add"(%i, %j) : (i64, i64) -> i64
    "func.return"(%gep, %add) : (!llvm.ptr, i64) -> ()
  }) : () -> ()
}) : () -> ()
