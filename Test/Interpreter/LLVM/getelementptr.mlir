// RUN: veir-interpret %s | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main"}> ({
    ^bb0():
      %size = "llvm.mlir.constant"() <{ "value" = 4 : i64 }> : () -> i64
      %array = "llvm.alloca"(%size) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      %off1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
      %ptr1 = "llvm.getelementptr"(%array, %off1) <{ elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %val1 = "llvm.mlir.constant"() <{ "value" = 256 : i64 }> : () -> i64
      "llvm.store"(%ptr1, %val1) : (!llvm.ptr, i64) -> ()
      %off2 = "llvm.mlir.constant"() <{ "value" = 9 : i64 }> : () -> i64
      %ptr2 = "llvm.getelementptr"(%array, %off2) <{ elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      %val2 = "llvm.load"(%ptr2) : (!llvm.ptr) -> i8
      "llvm.return"(%val2) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x01#8]
