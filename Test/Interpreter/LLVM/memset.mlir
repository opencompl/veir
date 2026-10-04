// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// `llvm.intr.memset` writes its byte to every byte of the range and leaves the
// bytes past it alone. A poison byte poisons the range.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i8, i32)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %byte = "llvm.mlir.constant"() <{value = -85 : i8}> : () -> i8
    %zero = "llvm.mlir.constant"() <{value = 0 : i8}> : () -> i8
    %poison = "llvm.mlir.poison"() : () -> i8
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%one, %p) : (i64, !llvm.ptr) -> ()
    "llvm.intr.memset"(%p, %byte, %eight) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    %all = "llvm.load"(%p) : (!llvm.ptr) -> i64
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.intr.memset"(%q, %zero, %eight) <{isVolatile = false}> : (!llvm.ptr, i8, i64) -> ()
    "llvm.intr.memset"(%q, %poison, %four) <{isVolatile = true}> : (!llvm.ptr, i8, i64) -> ()
    %low = "llvm.load"(%q) : (!llvm.ptr) -> i8
    %q4 = "llvm.getelementptr"(%q, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %high = "llvm.load"(%q4) : (!llvm.ptr) -> i32
    "func.return"(%all, %low, %high) : (i64, i8, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0xabababababababab#64, poison, 0x00000000#32]
