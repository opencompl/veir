// RUN: veir-interpret %s | filecheck %s

// A pointer read back from memory is wild: it finds its object when it is
// dereferenced, not when it is loaded. `%past` points at an address that no
// object covers yet. Were the reload decoded at load time it would be pinned
// to `%slot`, out of bounds, and the store would be UB. Being wild, it finds
// `%q`, which is allocated at that address in between.
// LLUBI: makes the store undefined behaviour (LLVM 23): for llubi the
// reloaded pointer keeps `%p`'s provenance and may not reach `%q`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %k = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %past = "llvm.getelementptr"(%p, %k) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%past, %slot) : (!llvm.ptr, !llvm.ptr) -> ()
    %r = "llvm.load"(%slot) : (!llvm.ptr) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %r) : (i64, !llvm.ptr) -> ()
    %res = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000007#64]
