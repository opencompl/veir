// RUN: veir-interpret %s | filecheck %s

// A `getelementptr` index scales by the element's allocation size, not its
// byte size, so tail padding counts. `!llvm.array<3 x i24>` is 12 bytes wide
// (three `i24`s at an `i32` alignment), not 9, which is where index 1 lands
// and where the `i8` load below reads it back from.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    ^bb0():
      %size = "llvm.mlir.constant"() <{ "value" = 4 : i64 }> : () -> i64
      %array = "llvm.alloca"(%size) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %off1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
      %ptr1 = "llvm.getelementptr"(%array, %off1) <{ elem_type = !llvm.array<3 x i24>, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %val1 = "llvm.mlir.constant"() <{ "value" = 7 : i8 }> : () -> i8
      "llvm.store"(%val1, %ptr1) : (i8, !llvm.ptr) -> ()
      %off2 = "llvm.mlir.constant"() <{ "value" = 12 : i64 }> : () -> i64
      %ptr2 = "llvm.getelementptr"(%array, %off2) <{ elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %val2 = "llvm.load"(%ptr2) : (!llvm.ptr) -> i8
      "llvm.return"(%val2) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8]
