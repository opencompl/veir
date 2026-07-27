// RUN: veir-interpret --memory-size 32 %s | filecheck %s
// RUN: veir-opt %s -p=canonicalize,instcombine,canonicalize,cse,dce,isel-br-riscv64,isel-sdag-riscv64,isel-riscv64,canonicalize,reconcile-cast,riscv-combine,dce > %t
// RUN: veir-interpret --memory-size 32 %t | filecheck %s

// Exercise the pointer-argument harness used by vsmith memory mode. The source
// function receives !llvm.ptr; after instruction selection and cast
// reconciliation the same argument is !riscv.reg.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 (!llvm.ptr)>}> ({
    ^bb0(%mem : !llvm.ptr):
      %slot = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
      %ptr = "llvm.getelementptr"(%mem, %slot) <{
        elem_type = i64,
        rawConstantIndices = array<i32: -2147483648>
      }> : (!llvm.ptr, i64) -> !llvm.ptr
      %value = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
      "llvm.store"(%value, %ptr) : (i64, !llvm.ptr) -> ()
      %loaded = "llvm.load"(%ptr) : (!llvm.ptr) -> i64
      "llvm.return"(%loaded) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
