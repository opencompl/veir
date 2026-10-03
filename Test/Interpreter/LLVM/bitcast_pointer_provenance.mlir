// RUN: veir-interpret %s | filecheck %s

// `llvm.bitcast` between pointer types hands the pointer through untouched, so it keeps the
// object the pointer came from. `%past` points one object further along than its own, and
// walking back from the bitcast pointer reaches the byte that was stored.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %k = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %mk = "llvm.mlir.constant"() <{value = -16 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    // The address of `%past` is the address of `%q`, but its object is still `%p`'s.
    %past = "llvm.getelementptr"(%p, %k) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %same = "llvm.bitcast"(%past) : (!llvm.ptr) -> !llvm.ptr
    %back = "llvm.getelementptr"(%same, %mk) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %res = "llvm.load"(%back) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
