// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// A global with an initializer region starts with the value the initializer
// returns.

// ALIVE_EXEC: crashes on a writable global.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i64, linkage = #llvm.linkage<internal>, sym_name = "g"}> ({
    %c = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    "llvm.return"(%c) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "main"}> ({
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %r = "llvm.load"(%g) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000007#64]
