// RUN: veir-interpret %s | filecheck %s

// The null pointer is a value, not poison: converting it to an integer
// gives zero. This is what distinguishes it from the poison pointer that
// the neighbouring tests produce.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %null = "llvm.mlir.zero"() : () -> !llvm.ptr
    %v = "llvm.ptrtoint"(%null) : (!llvm.ptr) -> i64
    "func.return"(%v) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000000#64]
