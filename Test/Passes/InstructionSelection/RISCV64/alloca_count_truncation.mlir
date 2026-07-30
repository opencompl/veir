// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// The element-count SSA value has type i8, so the literal 256 is truncated to
// zero. The selected stack slot must therefore have size 0, not 256 * 8.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "count_truncation", function_type = !llvm.func<void ()>}> ({
  ^bb0:
    %count = "llvm.mlir.constant"() <{value = 256 : i64}> : () -> i8
    %slot = "llvm.alloca"(%count) <{elem_type = i64}> : (i8) -> !llvm.ptr
    // CHECK: "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 0 : i64}> : () -> !riscv.reg
    "test.test"(%slot) : (!llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
