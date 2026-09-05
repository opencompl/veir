// RUN: veir-interpret %s | filecheck %s

// A copy carries the poison of what it copied: the source here is a fresh
// `alloca`, never written, so the destination reads back poison rather than a
// value the copy invented.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %n1 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
      %n4 = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
      %p = "llvm.alloca"(%n1) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
      %q = "llvm.alloca"(%n1) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
      "llvm.intr.memcpy"(%q, %p, %n4) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
      %v = "llvm.load"(%q) <{alignment = 4 : i64}> : (!llvm.ptr) -> i32
      "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison
