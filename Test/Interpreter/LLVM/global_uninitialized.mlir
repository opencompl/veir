// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// A global with neither a value nor an initializer starts as poison.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i64, linkage = #llvm.linkage<external>, sym_name = "g"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "main"}> ({
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %r = "llvm.load"(%g) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison]
