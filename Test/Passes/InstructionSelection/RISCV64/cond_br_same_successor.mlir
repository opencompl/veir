// RUN: veir-opt %s -p=isel-br-riscv64 2>&1 | filecheck %s

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<void (i1)>}> ({
    ^bb0(%cond : i1):
      "llvm.cond_br"(%cond) [^bb1, ^bb1] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i1) -> ()
    ^bb1():
      "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK-NOT: PANIC
// CHECK-NOT: Error: index out of bounds
// CHECK:      "builtin.module"()
// CHECK:      "riscv_cf.bnez"(%{{.*}}) [^[[DEST:[0-9]+]], ^[[DEST]]] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (!riscv.reg) -> ()
// CHECK:      ^[[DEST]]():
// CHECK-NEXT:   "llvm.return"() : () -> ()
// CHECK-NOT: PANIC
