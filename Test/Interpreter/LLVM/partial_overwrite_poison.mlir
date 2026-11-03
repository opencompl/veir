// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI
// RUN: ALIVE_EXEC_CHECK

// Memory is byte-granular: a byte stored into a stored integer replaces just
// that byte, and a poison integer stored over part of it poisons just those
// bytes. Store 0x0102030405060708, overwrite byte 3 with 0xaa and load the
// i64; then store a poison i32 over bytes 4..7 and load byte 1, byte 6 and
// the i64. Every access is naturally aligned.

// alive-exec reads all four results as poison: it gives no value to a load
// whose bytes do not all come from a single store of the loaded width.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i8, i8, i64)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %six = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 72623859790382856 : i64}> : () -> i64
    %aa = "llvm.mlir.constant"() <{value = -86 : i8}> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i32
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %p3 = "llvm.getelementptr"(%p, %three) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%aa, %p3) : (i8, !llvm.ptr) -> ()
    %whole = "llvm.load"(%p) : (!llvm.ptr) -> i64
    %p4 = "llvm.getelementptr"(%p, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%poison, %p4) : (i32, !llvm.ptr) -> ()
    %p1 = "llvm.getelementptr"(%p, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %byte1 = "llvm.load"(%p1) : (!llvm.ptr) -> i8
    %p6 = "llvm.getelementptr"(%p, %six) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %byte6 = "llvm.load"(%p6) : (!llvm.ptr) -> i8
    %after = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "func.return"(%whole, %byte1, %byte6, %after) : (i64, i8, i8, i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x01020304aa060708#64, 0x07#8, poison, poison]
// ALIVE_EXEC: Program output: #[poison, poison, poison, poison]
