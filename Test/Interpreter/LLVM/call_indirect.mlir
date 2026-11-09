// RUN: veir-interpret --ctree %s | filecheck %s
// RUN: LLUBI

// `main` calls a function through a pointer it loads, so the call stays indirect in LLVM IR.
// The callee pointer is not one of its arguments.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "id", function_type = !llvm.func<i32 (i32)>}> ({
  ^entry(%x : i32):
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %id = "llvm.mlir.addressof"() <{global_name = @id}> : () -> !llvm.ptr
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i32) -> !llvm.ptr
    "llvm.store"(%id, %slot) : (!llvm.ptr, !llvm.ptr) -> ()
    %f = "llvm.load"(%slot) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.call"(%f, %one) : (!llvm.ptr, i32) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
