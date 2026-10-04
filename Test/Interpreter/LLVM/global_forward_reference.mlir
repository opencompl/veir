// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// A global's initializer may take the address of a global defined after it.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = !llvm.ptr, linkage = #llvm.linkage<internal>, sym_name = "p"}> ({
    %q = "llvm.mlir.addressof"() <{global_name = @q}> : () -> !llvm.ptr
    "llvm.return"(%q) : (!llvm.ptr) -> ()
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<internal>, sym_name = "q", value = 7 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "main"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @p}> : () -> !llvm.ptr
    %q = "llvm.load"(%p) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000007#32]
