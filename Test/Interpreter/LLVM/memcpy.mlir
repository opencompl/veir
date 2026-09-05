// RUN: veir-interpret %s | filecheck %s

// `llvm.intr.memcpy` moves the bytes: the destination reads back what the
// source held, and the source is untouched.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %n1 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
      %n4 = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
      %b = "llvm.mlir.constant"() <{"value" = 7 : i8}> : () -> i8
      %p = "llvm.alloca"(%n1) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
      %q = "llvm.alloca"(%n1) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
      "llvm.intr.memset"(%p, %b, %n4) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
      "llvm.intr.memcpy"(%q, %p, %n4) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
      %v = "llvm.load"(%q) <{alignment = 4 : i64}> : (!llvm.ptr) -> i32
      "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x07070707#32]
