// RUN: not veir-interpret %s 2>&1 | filecheck %s
// RUN: ALIVE_EXEC_CHECK

// One byte more than `alloca_largest.mlir`: the object does not fit, which is
// a failure of the interpretation, not undefined behaviour.

// alive-exec does not model running out of memory and reads the byte back.
// llubi allocates the object for real and crashes, so it is not cross-checked.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %n = "llvm.mlir.constant"() <{value = -65552 : i64}> : () -> i64
    %seven = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %buf = "llvm.alloca"(%n) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "llvm.store"(%seven, %buf) : (i8, !llvm.ptr) -> ()
    %x = "llvm.load"(%buf) : (!llvm.ptr) -> i8
    "func.return"(%x) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      alloca_past_largest.mlir:14:5: error: failed to interpret operation
// CHECK-NEXT:     %buf = "llvm.alloca"(%n) <{elem_type = i8}> : (i64) -> !llvm.ptr
// CHECK-NEXT:     ^
// ALIVE_EXEC: Program output: #[0x07#8]
