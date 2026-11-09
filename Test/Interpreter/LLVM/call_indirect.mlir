// RUN: veir-interpret --ctree %s | filecheck %s

// `main` calls a function through its address. The callee pointer is not one of its arguments.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "id", function_type = !llvm.func<i32 (i32)>}> ({
  ^entry(%x : i32):
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i32 ()>}> ({
    %f = "llvm.mlir.addressof"() <{global_name = @id}> : () -> !llvm.ptr
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %r = "llvm.call"(%f, %one) : (!llvm.ptr, i32) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000001#32]
