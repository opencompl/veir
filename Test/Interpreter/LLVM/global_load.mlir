// RUN: veir-interpret %s | filecheck %s
// RUN: LLUBI

// A load through the address of a global reads its `value`.

// ALIVE_EXEC: crashes on a writable global.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "main"}> ({
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %r = "llvm.load"(%g) : (!llvm.ptr) -> i32
    "llvm.return"(%r) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000029#32]
