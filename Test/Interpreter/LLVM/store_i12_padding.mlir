// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: LLUBI_CHECK
// RUN: ALIVE_EXEC

// Storing an `i12` leaves the four bits past it in its second byte poison, even
// where memory held a value before, so an `i16` load of it is poison.
//
// alive-exec agrees. llubi stores the four bits as zeros instead, which refines
// poison.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i16 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %zero = "llvm.mlir.constant"() <{value = 0 : i16}> : () -> i16
    %v = "llvm.mlir.constant"() <{value = -1 : i12}> : () -> i12
    %p = "llvm.alloca"(%one) <{elem_type = i16}> : (i64) -> !llvm.ptr
    "llvm.store"(%zero, %p) : (i16, !llvm.ptr) -> ()
    "llvm.store"(%v, %p) : (i12, !llvm.ptr) -> ()
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i16
    "llvm.return"(%r) : (i16) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
// LLUBI: Program output: #[0x0fff#16]
