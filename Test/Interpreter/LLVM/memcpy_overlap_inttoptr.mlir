// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: LLUBI
// RUN: ALIVE_EXEC_CHECK

// `llvm.intr.memcpy` with partially overlapping ranges is UB, also when the
// destination is cast from an integer and so has no provenance of its own.
//
// alive-exec copies instead: its overlap check compares block ids, and the
// pointer cast from an integer does not carry the block id of `%buf`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %two = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %eight = "llvm.mlir.constant"() <{value = 8 : i64}> : () -> i64
    %buf = "llvm.alloca"(%two) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%one, %buf) : (i64, !llvm.ptr) -> ()
    %addr = "llvm.ptrtoint"(%buf) : (!llvm.ptr) -> i64
    %addr1 = "llvm.add"(%addr, %one) : (i64, i64) -> i64
    %buf1 = "llvm.inttoptr"(%addr1) : (i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%buf1, %buf, %eight) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %r = "llvm.load"(%buf) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
// ALIVE_EXEC: Program output: #[0x0000000000000001#64]
