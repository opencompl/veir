// RUN: veir-interpret --memory-size 32 %s | filecheck %s
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,reconcile-cast,riscv-combine,dce > %t
// RUN: veir-interpret --memory-size 32 %t | filecheck %s

// Exercise the pointer-argument harness used by vsmith memory mode. The source
// function receives !llvm.ptr; after instruction selection and cast
// reconciliation the same argument is !riscv.reg.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 (!llvm.ptr)>}> ({
    ^bb0(%mem : !llvm.ptr):
      %off2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
      %ptr2 = "llvm.getelementptr"(%mem, %off2) <{
        elem_type = i8,
        rawConstantIndices = array<i32: -2147483648>
      }> : (!llvm.ptr, i64) -> !llvm.ptr
      %off4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
      %ptr4 = "llvm.getelementptr"(%mem, %off4) <{
        elem_type = i8,
        rawConstantIndices = array<i32: -2147483648>
      }> : (!llvm.ptr, i64) -> !llvm.ptr

      %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
      "llvm.store"(%zero, %mem) : (i64, !llvm.ptr) -> ()
      %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
      %one8 = "llvm.trunc"(%one) : (i64) -> i8
      "llvm.store"(%one8, %mem) : (i8, !llvm.ptr) -> ()
      %two16 = "llvm.trunc"(%off2) : (i64) -> i16
      "llvm.store"(%two16, %ptr2) : (i16, !llvm.ptr) -> ()
      %four32 = "llvm.trunc"(%off4) : (i64) -> i32
      "llvm.store"(%four32, %ptr4) : (i32, !llvm.ptr) -> ()

      %load8 = "llvm.load"(%mem) : (!llvm.ptr) -> i8
      %load16 = "llvm.load"(%ptr2) : (!llvm.ptr) -> i16
      %load32 = "llvm.load"(%ptr4) : (!llvm.ptr) -> i32
      %load64 = "llvm.load"(%mem) : (!llvm.ptr) -> i64
      %ext8 = "llvm.zext"(%load8) : (i8) -> i64
      %ext16 = "llvm.zext"(%load16) : (i16) -> i64
      %ext32 = "llvm.zext"(%load32) : (i32) -> i64
      %xor8 = "llvm.xor"(%load64, %ext8) : (i64, i64) -> i64
      %xor16 = "llvm.xor"(%xor8, %ext16) : (i64, i64) -> i64
      %result = "llvm.xor"(%xor16, %ext32) : (i64, i64) -> i64
      "llvm.return"(%result) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000400020006#64]
