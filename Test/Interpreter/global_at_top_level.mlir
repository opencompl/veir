// RUN: veir-interpret %s | filecheck %s

// An `llvm.mlir.global` alongside `@main` is a legal top-level op; the
// interpreter must skip past it when looking for the entry point.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", unnamed_addr = 0 : i64, value = 41 : i32, visibility_ = 0 : i64}> ({
  }) : () -> ()
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<i32 ()>, linkage = #llvm.linkage<external>, sym_name = "main", visibility_ = 0 : i64}> ({
    %x = "llvm.mlir.constant"() <{value = 5 : i32}> : () -> i32
    "llvm.return"(%x) : (i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000005#32]
