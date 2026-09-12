// RUN: veir-interpret %s | filecheck %s

// A pointer cast to an integer is its physical address, and casting that
// address back yields a pointer into the same object. Object 0 is null, so
// the first allocation lands at address 16.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, !llvm.byte<64>)}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %addr = "llvm.bitcast"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    %q = "llvm.bitcast"(%addr) : (!llvm.byte<64>) -> !llvm.ptr
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "func.return"(%r, %addr) : (i64, !llvm.byte<64>) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64, 0b0000000000000000000000000000000000000000000000000000000000010000#64]
