// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t
// RUN: not grep -E '"llvm\.(load|store)"' %t

// Pointers are loaded from stack slots and stored back swapped, then one is
// copied through a third slot. The selected code must reach the same objects
// the LLVM-level program does, with every pointer access selected to
// `riscv.ld` / `riscv.sd`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %one = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
      %ten = "llvm.mlir.constant"() <{ "value" = 10 : i64 }> : () -> i64
      %three = "llvm.mlir.constant"() <{ "value" = 3 : i64 }> : () -> i64
      %a = "llvm.alloca"(%one) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %b = "llvm.alloca"(%one) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %sa = "llvm.alloca"(%one) <{ "elem_type" = !llvm.ptr }> : (i64) -> !llvm.ptr
      %sb = "llvm.alloca"(%one) <{ "elem_type" = !llvm.ptr }> : (i64) -> !llvm.ptr
      %sc = "llvm.alloca"(%one) <{ "elem_type" = !llvm.ptr }> : (i64) -> !llvm.ptr
      "llvm.store"(%ten, %a) : (i64, !llvm.ptr) -> ()
      "llvm.store"(%three, %b) : (i64, !llvm.ptr) -> ()
      "llvm.store"(%a, %sa) : (!llvm.ptr, !llvm.ptr) -> ()
      "llvm.store"(%b, %sb) : (!llvm.ptr, !llvm.ptr) -> ()
      %pa = "llvm.load"(%sa) : (!llvm.ptr) -> !llvm.ptr
      %pb = "llvm.load"(%sb) : (!llvm.ptr) -> !llvm.ptr
      "llvm.store"(%pb, %sa) : (!llvm.ptr, !llvm.ptr) -> ()
      "llvm.store"(%pa, %sb) : (!llvm.ptr, !llvm.ptr) -> ()
      %qa = "llvm.load"(%sa) : (!llvm.ptr) -> !llvm.ptr
      "llvm.store"(%qa, %sc) : (!llvm.ptr, !llvm.ptr) -> ()
      %qc = "llvm.load"(%sc) : (!llvm.ptr) -> !llvm.ptr
      %qb = "llvm.load"(%sb) : (!llvm.ptr) -> !llvm.ptr
      %x = "llvm.load"(%qc) : (!llvm.ptr) -> i64
      %y = "llvm.load"(%qb) : (!llvm.ptr) -> i64
      %out = "llvm.sub"(%x, %y) : (i64, i64) -> i64
      "llvm.return"(%out) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// SRC: Program output: #[0xfffffffffffffff9#64]
// CHECK: Program output: #[0xfffffffffffffff9#64]

// ISEL:     "riscv_stack.alloca"
// ISEL:     "riscv_stack.alloca"
// ISEL:     %[[SA:.*]] = "riscv_stack.alloca"
// ISEL:     %[[SB:.*]] = "riscv_stack.alloca"
// ISEL:     %[[PA:.*]] = "riscv.ld"(%[[SA]]) <{"value" = 0 : i64}>
// ISEL:     %[[PB:.*]] = "riscv.ld"(%[[SB]]) <{"value" = 0 : i64}>
// ISEL:     "riscv.sd"(%[[PB]], %[[SA]]) <{"value" = 0 : i64}>
// ISEL:     "riscv.sd"(%[[PA]], %[[SB]]) <{"value" = 0 : i64}>
