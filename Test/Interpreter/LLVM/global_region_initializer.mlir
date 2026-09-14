// RUN: veir-interpret %s | filecheck %s

// A global with an initializer region starts with the value the region returns.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i64, linkage = #llvm.linkage<internal>, sym_name = "g"}> ({
    %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %d = "llvm.mul"(%c, %c) : (i64, i64) -> i64
    "llvm.return"(%d) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "main"}> ({
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %r = "llvm.load"(%g) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000031#64]
