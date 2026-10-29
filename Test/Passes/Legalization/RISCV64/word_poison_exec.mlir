// RUN: veir-interpret %s | filecheck %s
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t
// RUN: veir-interpret %t | filecheck %s

// Flags are evaluated at 32 bits even though the legalized operations use i64.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32, i32, i32, i32)}> ({
    %max = "llvm.mlir.constant"() <{value = 2147483647 : i32}> : () -> i32
    %zero = "llvm.mlir.constant"() <{value = 0 : i32}> : () -> i32
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %two = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %three = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %thirtytwo = "llvm.mlir.constant"() <{value = 32 : i32}> : () -> i32
    %add = "llvm.add"(%max, %one) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %sub = "llvm.sub"(%zero, %one) <{overflowFlags = 2 : i32}> : (i32, i32) -> i32
    %mul = "llvm.mul"(%max, %two) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %sdiv = "llvm.sdiv"(%three, %two) <{isExact}> : (i32, i32) -> i32
    %udiv = "llvm.udiv"(%three, %two) <{isExact}> : (i32, i32) -> i32
    %shl = "llvm.shl"(%max, %one) <{overflowFlags = 1 : i32}> : (i32, i32) -> i32
    %lshr = "llvm.lshr"(%three, %one) <{isExact}> : (i32, i32) -> i32
    %ashr = "llvm.ashr"(%three, %one) <{isExact}> : (i32, i32) -> i32
    %overshift = "llvm.shl"(%one, %thirtytwo) : (i32, i32) -> i32
    "func.return"(%add, %sub, %mul, %sdiv, %udiv, %shl, %lshr, %ashr, %overshift) : (i32, i32, i32, i32, i32, i32, i32, i32, i32) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[poison, poison, poison, poison, poison, poison, poison, poison, poison]
