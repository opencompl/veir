// RUN: veir-interpret %s | filecheck %s

// A pointer converted to its physical address and back denotes the same
// object, so the load through the reconstructed pointer sees the stored
// value. The address itself is not returned: VeIR chooses its own layout,
// so the number would mean nothing outside this interpreter.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> i64}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %addr = "llvm.bitcast"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    %q = "llvm.bitcast"(%addr) : (!llvm.byte<64>) -> !llvm.ptr
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "func.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
