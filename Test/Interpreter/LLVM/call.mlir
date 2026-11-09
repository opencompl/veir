// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: LLUBI

// The callee writes through a pointer from `main`, which then reads the store.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "store_one", function_type = !llvm.func<void (ptr)>}> ({
  ^entry(%p : !llvm.ptr):
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    "llvm.store"(%one, %p) : (i32, !llvm.ptr) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i32}> : (i64) -> !llvm.ptr
    "llvm.call"(%p) <{callee = @store_one}> : (!llvm.ptr) -> ()
    %x = "llvm.load"(%p) : (!llvm.ptr) -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
