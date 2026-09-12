// RUN: veir-interpret %s | filecheck %s

// A string-valued global holds its bytes verbatim.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, constant, global_type = !llvm.array<3 x i8>, linkage = #llvm.linkage<internal>, sym_name = "s", value = "hi\00"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i8 ()>, sym_name = "main"}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %s = "llvm.mlir.addressof"() <{global_name = @s}> : () -> !llvm.ptr
    %s1 = "llvm.getelementptr"(%s, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %c = "llvm.load"(%s1) : (!llvm.ptr) -> i8
    "llvm.return"(%c) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x69#8]
