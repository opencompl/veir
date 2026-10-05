// RUN: not veir-opt %s 2>&1 | filecheck %s
// RUN: MLIR_INVALID

// A lifetime marker bounds the object behind a pointer, so an integer operand
// is not something it can mark.
"builtin.module"() ({
  "llvm.func"() <{function_type = !llvm.func<void (i32)>, linkage = #llvm.linkage<external>, sym_name = "f"}> ({
  ^bb0(%x: i32):
    "llvm.intr.lifetime.start"(%x) : (i32) -> ()
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Expected operand 0 to have !llvm.ptr type
