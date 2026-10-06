// RUN: veir-interpret %s | filecheck %s

// `%past` has `%p`'s provenance and `%q`'s address, so a store through it is
// out of bounds, as in `alloca_out_of_bounds.mlir`. Through an integer and
// back the pointer is wild, the store finds `%q` at its address, and a load
// from `%q` sees it.
//
// LLUBI: reports undefined behaviour, since for it the reconstructed pointer
// may not reach `%q`.
//
// ALIVE_EXEC: returns poison: its layout need not place `%q` sixteen bytes
// past `%p`, and its provenance rule only lets an integer reach an exposed
// object.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %k = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %past = "llvm.getelementptr"(%p, %k) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %addr = "llvm.ptrtoint"(%past) : (!llvm.ptr) -> i64
    %same = "llvm.inttoptr"(%addr) : (i64) -> !llvm.ptr
    "llvm.store"(%v, %same) : (i64, !llvm.ptr) -> ()
    %res = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000007#64]
