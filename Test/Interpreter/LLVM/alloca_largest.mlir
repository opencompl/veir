// RUN: veir-interpret %s | filecheck %s
// RUN: ALIVE_EXEC

// The largest alloca that fits: its guard byte is the last address, 2^64 - 1.
// The size follows from where the allocator places the first alloca.
// `alloca_past_largest.mlir` asks for one byte more.

// llubi allocates the object for real and crashes, so it is not cross-checked.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i8}> ({
    %n = "llvm.mlir.constant"() <{value = -65553 : i64}> : () -> i64
    %seven = "llvm.mlir.constant"() <{value = 7 : i8}> : () -> i8
    %buf = "llvm.alloca"(%n) <{elem_type = i8}> : (i64) -> !llvm.ptr
    "llvm.store"(%seven, %buf) : (i8, !llvm.ptr) -> ()
    %x = "llvm.load"(%buf) : (!llvm.ptr) -> i8
    "func.return"(%x) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x07#8]
