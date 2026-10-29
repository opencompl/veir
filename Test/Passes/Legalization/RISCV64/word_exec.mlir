// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t
// RUN: veir-interpret %t | filecheck %s
// RUN: veir-opt %t --print-op-generic -p=postlegalizer-combiner-riscv64,isel-riscv64,reconcile-cast,riscv-combine,dce > %t.selected
// RUN: veir-interpret %t.selected | filecheck %s

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32, i32, i32, i32)}> ({
    // Exercise every binary custom legalization and its ordinary instruction selection.
    %x = "llvm.mlir.constant"() <{value = -2 : i32}> : () -> i32
    %two = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %add = "llvm.add"(%x, %two) : (i32, i32) -> i32
    %sub = "llvm.sub"(%x, %two) : (i32, i32) -> i32
    %mul = "llvm.mul"(%x, %two) : (i32, i32) -> i32
    %sdiv = "llvm.sdiv"(%x, %two) <{isExact}> : (i32, i32) -> i32
    %udiv = "llvm.udiv"(%x, %one) <{isExact}> : (i32, i32) -> i32
    %urem = "llvm.urem"(%x, %two) : (i32, i32) -> i32
    %shl = "llvm.shl"(%x, %one) : (i32, i32) -> i32
    %lshr = "llvm.lshr"(%x, %one) <{isExact}> : (i32, i32) -> i32
    %ashr = "llvm.ashr"(%x, %one) <{isExact}> : (i32, i32) -> i32
    "func.return"(%add, %sub, %mul, %sdiv, %udiv, %urem, %shl, %lshr, %ashr) : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x00000000#32, 0xfffffffc#32, 0xfffffffc#32, 0xffffffff#32, 0xfffffffe#32, 0x00000000#32, 0xfffffffc#32, 0x7fffffff#32, 0xffffffff#32]
