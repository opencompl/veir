// RUN: veir-interpret %s | filecheck %s

// The byte `llvm.intr.memset` writes is read, so a poison byte is immediate
// undefined behaviour: the operation has no result to be poisoned instead.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    ^entry():
      %n1 = "llvm.mlir.constant"() <{"value" = 1 : i64}> : () -> i64
      %n4 = "llvm.mlir.constant"() <{"value" = 4 : i64}> : () -> i64
      %b = "llvm.mlir.poison"() : () -> i8
      %p = "llvm.alloca"(%n1) <{alignment = 4 : i64, elem_type = i32}> : (i64) -> !llvm.ptr
      "llvm.intr.memset"(%p, %b, %n4) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
      %v = "llvm.load"(%p) <{alignment = 4 : i64}> : (!llvm.ptr) -> i32
      "llvm.return"(%v) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
