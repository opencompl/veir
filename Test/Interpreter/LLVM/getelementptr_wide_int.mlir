// RUN: veir-interpret %s | filecheck %s

// A width with no layout entry of its own takes the alignment of the largest
// entry, `i128:128`. An `i200` therefore occupies 25 bytes but strides by 32,
// which is where index 1 lands and where the `i8` load reads it back from.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    ^bb0():
      %size = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
      %array = "llvm.alloca"(%size) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %off1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
      %ptr1 = "llvm.getelementptr"(%array, %off1) <{ elem_type = i200, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %val1 = "llvm.mlir.constant"() <{ "value" = 5 : i8 }> : () -> i8
      "llvm.store"(%val1, %ptr1) : (i8, !llvm.ptr) -> ()
      %off2 = "llvm.mlir.constant"() <{ "value" = 32 : i64 }> : () -> i64
      %ptr2 = "llvm.getelementptr"(%array, %off2) <{ elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %val2 = "llvm.load"(%ptr2) : (!llvm.ptr) -> i8
      "llvm.return"(%val2) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x05#8]
