// RUN: not veir2mir %s > %t.out 2> %t.err
// RUN: filecheck %s --input-file=%t.err
// RUN: test ! -s %t.out

// A region requiring constant-expression translation must fail, even when the
// global is unused. Buffered output must also discard the preceding definition.
"builtin.module"() ({
  "llvm.mlir.global"() <{global_type = i32, linkage = #llvm.linkage<external>, sym_name = "data", value = 7 : i32}> ({}) : () -> ()
  "llvm.mlir.global"() <{global_type = !llvm.ptr, linkage = #llvm.linkage<external>, sym_name = "interior"}> ({
    %p = "llvm.mlir.addressof"() <{global_name = @data}> : () -> !llvm.ptr
    %q = "llvm.getelementptr"(%p) <{elem_type = i8, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
    "llvm.return"(%q) : (!llvm.ptr) -> ()
  }) : () -> ()
  "riscv_cf.func"() <{function_type = () -> (), sym_name = "main"}> ({
    "riscv_cf.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: veir2mir: error: global @interior: unsupported initializer operation 'llvm.getelementptr'
