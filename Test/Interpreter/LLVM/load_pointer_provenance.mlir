// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: LLUBI_CHECK
// RUN: ALIVE_EXEC_CHECK

// A pointer read back from memory has no provenance: it reaches whichever
// object its address lies in at each access. `%past` points at an address no
// object covers when it is stored, but `%q` is allocated at that address
// before the store through the reload, which writes to `%q`.
//
// llubi and alive-exec report undefined behaviour instead. For them the
// reload keeps the provenance of `%p`, so the store is out of its bounds.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %k = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %past = "llvm.getelementptr"(%p, %k) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%past, %slot) : (!llvm.ptr, !llvm.ptr) -> ()
    %r = "llvm.load"(%slot) : (!llvm.ptr) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%one, %r) : (i64, !llvm.ptr) -> ()
    %res = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
// LLUBI: Undefined behavior
// ALIVE_EXEC: Undefined behavior
