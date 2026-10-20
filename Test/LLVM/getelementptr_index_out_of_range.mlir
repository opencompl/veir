// RUN: not veir-opt %s 2>&1 | filecheck %s

// A raw index must fit in an i32, signed or unsigned; it does not wrap.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (ptr)>, sym_name = "f"}> ({
  ^bb0(%p: !llvm.ptr):
    %q = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<(i8, i64)>, rawConstantIndices = array<i32: 0, 4294967297>}> : (!llvm.ptr) -> !llvm.ptr
    // CHECK: getelementptr: raw constant index 4294967297 does not fit in i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()
