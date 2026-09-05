// RUN: veir-interpret %s | filecheck %s

// `llvm.intr.memmove` is the overlapping copy: shifting a buffer down by one
// byte reads every source byte before it is overwritten, which is exactly what
// `llvm.intr.memcpy` refuses to promise.
//
// The four bytes start 01 02 03 04 (little-endian 0x04030201); moving the top
// three down one byte leaves 02 03 04 04, i.e. 0x04040302.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %n1 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
      %n3 = "llvm.mlir.constant"() <{"value" = 3 : i64}> : () -> i64
      %init = "llvm.mlir.constant"() <{"value" = 67305985 : i32}> : () -> i32
      %p = "llvm.alloca"(%n1) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
      "llvm.store"(%init, %p) <{alignment = 4 : i64}> : (i32, !llvm.ptr) -> ()
      %one = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
      %q = "llvm.getelementptr"(%p, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
      "llvm.intr.memmove"(%p, %q, %n3) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
      %v = "llvm.load"(%p) <{alignment = 4 : i64}> : (!llvm.ptr) -> i32
      "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x04040302#32]
