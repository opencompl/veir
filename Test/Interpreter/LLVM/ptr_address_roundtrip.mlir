// RUN: veir-interpret %s | filecheck %s
// RUN: %if llubi-min-24 %{ LLUBI %} %else %{ LLUBI_CHECK %}

// A pointer converted to its physical address and back denotes the same
// object, so the load through the reconstructed pointer sees the stored
// value.

// Until LLVM 24, llubi called a byte holding pointer bits undefined behavior.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%one, %p) : (i64, !llvm.ptr) -> ()
    %addr = "llvm.bitcast"(%p) : (!llvm.ptr) -> !llvm.byte<64>
    %q = "llvm.bitcast"(%addr) : (!llvm.byte<64>) -> !llvm.ptr
    %r = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
// LLUBI: Undefined behavior
