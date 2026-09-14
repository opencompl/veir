// RUN: veir-interpret %s | filecheck %s

// `alloca` reserves one allocation size per element, so an `i1` still takes a
// whole byte and the eight bytes reserved here are enough to store into.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i8 ()>}> ({
    ^bb0():
      %count = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64
      %buf = "llvm.alloca"(%count) <{ "elem_type" = i1 }> : (i64) -> !llvm.ptr
      %val = "llvm.mlir.constant"() <{ "value" = 3 : i8 }> : () -> i8
      "llvm.store"(%val, %buf) : (i8, !llvm.ptr) -> ()
      %loaded = "llvm.load"(%buf) : (!llvm.ptr) -> i8
      "llvm.return"(%loaded) : (i8) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x03#8]
