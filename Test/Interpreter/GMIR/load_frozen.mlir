// RUN: veir-interpret %s | filecheck %s

// gMIR has no byte type, so `g_load` loads an integer and freezes its poison
// bits to 0, unless every bit is poison; then we keep the poison.
// This test confirms this behavior: We poison the lowest byte and ensure that
// it is read as zeros.
// TODO: With CTrees, the frozen bits should be chosen nondeterministically.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %c = "llvm.mlir.constant"() <{value = 0x11223344 : i32}> : () -> i32
    "gmir.g_store"(%c, %p) <{alignment = 4 : i64, size = 32 : i64}> : (i32, !llvm.ptr) -> ()
    %poison = "llvm.mlir.poison"() : () -> i8
    "llvm.store"(%poison, %p) : (i8, !llvm.ptr) -> ()
    %x = "gmir.g_load"(%p) <{alignment = 4 : i64, size = 32 : i64}> : (!llvm.ptr) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x11223300#32]
