// RUN: not veir2mir %s > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

// A top-level operation that is neither a function, a global nor module flags
// would be silently lost.
"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g"}> ({}) : () -> ()
  "llvm.mlir.alias"() <{alias_type = i32, linkage = #llvm.linkage<external>, sym_name = "a", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    "llvm.return"(%0) : (!llvm.ptr) -> ()
  }) : () -> ()
  "riscv_cf.func"() <{sym_name = "main", function_type = () -> ()}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: unsupported top-level operation 'llvm.mlir.alias'
