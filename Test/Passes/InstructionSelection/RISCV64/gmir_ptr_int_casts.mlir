// RUN: veir-opt %s --print-op-generic -p=riscv | filecheck %s

// A pointer is its address in a register, so casting it to an `i64` and back is free.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "advance", function_type = !llvm.func<ptr (ptr)>}> ({
  ^bb0(%p : !llvm.ptr):
    // CHECK-LABEL: "sym_name" = "advance"
    // CHECK-NEXT:  ^{{.*}}(%[[P:.*]] : !riscv.reg):
    // CHECK-NEXT:  %[[Q:.*]] = "riscv.addi"(%[[P]]) <{"value" = 8 : i64}>
    // CHECK-NEXT:  "riscv_cf.return"(%[[Q]])
    %i = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %j = "llvm.add"(%i, %eight) : (i64, i64) -> i64
    %q = "llvm.inttoptr"(%j) : (i64) -> !llvm.ptr
    "llvm.return"(%q) : (!llvm.ptr) -> ()
  }) : () -> ()
}) : () -> ()
