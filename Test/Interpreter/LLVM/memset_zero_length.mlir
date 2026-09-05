// RUN: veir-interpret %s | filecheck %s

// A zero length writes nothing at all, so what was in the destination survives
// -- and a zero-length copy of a null pointer is not undefined behaviour.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %n0 = "llvm.mlir.constant"() <{"value" = 0 : i64}> : () -> i64
      %n1 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
      %n4 = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
      %b7 = "llvm.mlir.constant"() <{"value" = 7 : i8}> : () -> i8
      %b9 = "llvm.mlir.constant"() <{"value" = 9 : i8}> : () -> i8
      %p = "llvm.alloca"(%n1) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
      "llvm.intr.memset"(%p, %b7, %n4) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
      "llvm.intr.memset"(%p, %b9, %n0) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
      %v = "llvm.load"(%p) <{alignment = 4 : i64}> : (!llvm.ptr) -> i32
      "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x07070707#32]
