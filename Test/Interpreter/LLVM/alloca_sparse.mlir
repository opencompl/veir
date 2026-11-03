// RUN: veir-interpret %s | filecheck %s
// RUN: ALIVE_EXEC

// A 4 GiB alloca of which only the first and the last byte are touched: an
// object costs nothing until it is written to.

// llubi allocates the object for real and crashes, so it is not cross-checked.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i8, i8)}> ({
    %n = "llvm.mlir.constant"() <{value = 4294967296 : i64}> : () -> i64
    %last = "llvm.mlir.constant"() <{value = 4294967295 : i64}> : () -> i64
    %a = "llvm.mlir.constant"() <{value = 40 : i8}> : () -> i8
    %b = "llvm.mlir.constant"() <{value = 2 : i8}> : () -> i8
    %buf = "llvm.alloca"(%n) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %end = "llvm.getelementptr"(%buf, %last) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%a, %buf) : (i8, !llvm.ptr) -> ()
    "llvm.store"(%b, %end) : (i8, !llvm.ptr) -> ()
    %first = "llvm.load"(%buf) : (!llvm.ptr) -> i8
    %final = "llvm.load"(%end) : (!llvm.ptr) -> i8
    "func.return"(%first, %final) : (i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x28#8, 0x02#8]
