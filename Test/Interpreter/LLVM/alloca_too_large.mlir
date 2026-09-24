// RUN: veir-interpret %s | filecheck %s

// An `alloca` cannot report failure, so reserving more bytes than the address
// space holds is UB: 2^62 elements of 8 bytes is 2^65 bytes.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    ^bb0():
      %count = "llvm.mlir.constant"() <{ "value" = 4611686018427387904 : i64 }> : () -> i64
      %buf = "llvm.alloca"(%count) <{ "elem_type" = i64 }> : (i64) -> !llvm.ptr
      "llvm.return"(%count) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
