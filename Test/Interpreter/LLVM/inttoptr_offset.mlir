// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// Address arithmetic between the casts: the integer moves within the object,
// and the pointer cast back from it reads the element at that offset.
// Alive2 agrees (alive-exec): the function returns 7, non-poison.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %p = "llvm.alloca"(%two) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %s = "llvm.getelementptr"(%p, %one) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v, %s) : (i64, !llvm.ptr) -> ()
    %a = "llvm.ptrtoint"(%p) : (!llvm.ptr) -> i64
    %b = "llvm.add"(%a, %eight) : (i64, i64) -> i64
    %q = "llvm.inttoptr"(%b) : (i64) -> !llvm.ptr
    %res = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000007#64]
