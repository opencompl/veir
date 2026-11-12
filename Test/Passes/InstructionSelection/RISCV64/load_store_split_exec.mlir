// RUN: veir-opt %s --print-op-generic -p=riscv > %t && veir-interpret %t | filecheck %s

// XFAIL: *
// Needs `lowerSext`, commented out of the pass as unproven.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %two = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
      %buf = "llvm.alloca"(%two) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %ones = "llvm.mlir.constant"() <{ "value" = -1 : i64 }> : () -> i64
      %eight = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
      %three = "llvm.mlir.constant"() <{ "value" = 3 : i64 }> : () -> i64
      %hi = "llvm.getelementptr"(%buf, %eight) <{ elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %p = "llvm.getelementptr"(%buf, %three) <{ elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %c = "llvm.mlir.constant"() <{ "value" = -6795364578871345152 : i64 }> : () -> i64
      %k = "llvm.mlir.constant"() <{ "value" = 1000003 : i64 }> : () -> i64
      %acc0 = "llvm.mlir.constant"() <{ "value" = 0 : i64 }> : () -> i64

      "llvm.store"(%ones, %buf) : (i64, !llvm.ptr) -> ()
      "llvm.store"(%ones, %hi) : (i64, !llvm.ptr) -> ()
      %t24 = "llvm.trunc"(%c) : (i64) -> i24
      "llvm.store"(%t24, %p) <{alignment = 1 : i64}> : (i24, !llvm.ptr) -> ()
      %l24 = "llvm.load"(%p) <{alignment = 1 : i64}> : (!llvm.ptr) -> i24
      %z24 = "llvm.zext"(%l24) : (i24) -> i64
      %s24 = "llvm.sext"(%l24) : (i24) -> i64
      %w24a = "llvm.load"(%buf) : (!llvm.ptr) -> i64
      %w24b = "llvm.load"(%hi) : (!llvm.ptr) -> i64
      %h24a = "llvm.mul"(%z24, %k) : (i64, i64) -> i64
      %h24b = "llvm.add"(%h24a, %s24) : (i64, i64) -> i64
      %h24c = "llvm.mul"(%h24b, %k) : (i64, i64) -> i64
      %h24d = "llvm.add"(%h24c, %w24a) : (i64, i64) -> i64
      %h24e = "llvm.mul"(%h24d, %k) : (i64, i64) -> i64
      %h24f = "llvm.add"(%h24e, %w24b) : (i64, i64) -> i64
      %acc1 = "llvm.add"(%acc0, %h24f) : (i64, i64) -> i64

      "llvm.store"(%ones, %buf) : (i64, !llvm.ptr) -> ()
      "llvm.store"(%ones, %hi) : (i64, !llvm.ptr) -> ()
      %t40 = "llvm.trunc"(%c) : (i64) -> i40
      "llvm.store"(%t40, %p) <{alignment = 1 : i64}> : (i40, !llvm.ptr) -> ()
      %l40 = "llvm.load"(%p) <{alignment = 1 : i64}> : (!llvm.ptr) -> i40
      %z40 = "llvm.zext"(%l40) : (i40) -> i64
      %s40 = "llvm.sext"(%l40) : (i40) -> i64
      %w40a = "llvm.load"(%buf) : (!llvm.ptr) -> i64
      %w40b = "llvm.load"(%hi) : (!llvm.ptr) -> i64
      %h40a = "llvm.mul"(%z40, %k) : (i64, i64) -> i64
      %h40b = "llvm.add"(%h40a, %s40) : (i64, i64) -> i64
      %h40c = "llvm.mul"(%h40b, %k) : (i64, i64) -> i64
      %h40d = "llvm.add"(%h40c, %w40a) : (i64, i64) -> i64
      %h40e = "llvm.mul"(%h40d, %k) : (i64, i64) -> i64
      %h40f = "llvm.add"(%h40e, %w40b) : (i64, i64) -> i64
      %acc2 = "llvm.add"(%acc1, %h40f) : (i64, i64) -> i64

      "llvm.store"(%ones, %buf) : (i64, !llvm.ptr) -> ()
      "llvm.store"(%ones, %hi) : (i64, !llvm.ptr) -> ()
      %t48 = "llvm.trunc"(%c) : (i64) -> i48
      "llvm.store"(%t48, %p) <{alignment = 1 : i64}> : (i48, !llvm.ptr) -> ()
      %l48 = "llvm.load"(%p) <{alignment = 1 : i64}> : (!llvm.ptr) -> i48
      %z48 = "llvm.zext"(%l48) : (i48) -> i64
      %s48 = "llvm.sext"(%l48) : (i48) -> i64
      %w48a = "llvm.load"(%buf) : (!llvm.ptr) -> i64
      %w48b = "llvm.load"(%hi) : (!llvm.ptr) -> i64
      %h48a = "llvm.mul"(%z48, %k) : (i64, i64) -> i64
      %h48b = "llvm.add"(%h48a, %s48) : (i64, i64) -> i64
      %h48c = "llvm.mul"(%h48b, %k) : (i64, i64) -> i64
      %h48d = "llvm.add"(%h48c, %w48a) : (i64, i64) -> i64
      %h48e = "llvm.mul"(%h48d, %k) : (i64, i64) -> i64
      %h48f = "llvm.add"(%h48e, %w48b) : (i64, i64) -> i64
      %acc3 = "llvm.add"(%acc2, %h48f) : (i64, i64) -> i64

      "llvm.store"(%ones, %buf) : (i64, !llvm.ptr) -> ()
      "llvm.store"(%ones, %hi) : (i64, !llvm.ptr) -> ()
      %t56 = "llvm.trunc"(%c) : (i64) -> i56
      "llvm.store"(%t56, %p) <{alignment = 1 : i64}> : (i56, !llvm.ptr) -> ()
      %l56 = "llvm.load"(%p) <{alignment = 1 : i64}> : (!llvm.ptr) -> i56
      %z56 = "llvm.zext"(%l56) : (i56) -> i64
      %s56 = "llvm.sext"(%l56) : (i56) -> i64
      %w56a = "llvm.load"(%buf) : (!llvm.ptr) -> i64
      %w56b = "llvm.load"(%hi) : (!llvm.ptr) -> i64
      %h56a = "llvm.mul"(%z56, %k) : (i64, i64) -> i64
      %h56b = "llvm.add"(%h56a, %s56) : (i64, i64) -> i64
      %h56c = "llvm.mul"(%h56b, %k) : (i64, i64) -> i64
      %h56d = "llvm.add"(%h56c, %w56a) : (i64, i64) -> i64
      %h56e = "llvm.mul"(%h56d, %k) : (i64, i64) -> i64
      %h56f = "llvm.add"(%h56e, %w56b) : (i64, i64) -> i64
      %acc4 = "llvm.add"(%acc3, %h56f) : (i64, i64) -> i64
      "llvm.return"(%acc4) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xbe3a0d7bc062a7f8#64]
