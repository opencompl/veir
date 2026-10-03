// RUN: veir-interpret %s | filecheck %s

// A wild pointer is more permissive than the pointer it came from. `%past` has `%p`'s
// provenance and `%q`'s address, so a store through it is out of bounds, as in
// `alloca_out_of_bounds.mlir`. Through an integer and back the same address names no object,
// the store finds `%q`, and a load from `%q` sees it.
// TODO: Alive2 (alive-exec) diverges: its symbolic layout need not place `%q`
// sixteen bytes past `%p`, and its provenance rule only lets an integer reach
// exposed objects, so the store never lands in `%q` there and it returns 0.
// llubi (LLVM 23) agrees that the store does not reach `%q`: it reports
// undefined behaviour.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %k = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %past = "llvm.getelementptr"(%p, %k) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %addr = "llvm.ptrtoint"(%past) : (!llvm.ptr) -> i64
    %wild = "llvm.inttoptr"(%addr) : (i64) -> !llvm.ptr
    "llvm.store"(%v, %wild) : (i64, !llvm.ptr) -> ()
    %res = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000007#64]
