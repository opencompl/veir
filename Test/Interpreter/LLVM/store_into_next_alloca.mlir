// RUN: veir-interpret %s | filecheck %s
// RUN: CTREE
// RUN: LLUBI_CHECK
// RUN: ALIVE_EXEC_CHECK

// A pointer past the end of `%p` that lies in `%q` stores to `%q`: we do not
// yet model provenance, so an access may access data in any object.
//
// llubi and alive-exec report undefined behaviour instead, as the store is out
// of the bounds of `%p`, whose provenance `%past` carries.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %sixteen = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %past = "llvm.getelementptr"(%p, %sixteen) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%one, %past) : (i64, !llvm.ptr) -> ()
    %res = "llvm.load"(%q) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x0000000000000001#64]
// LLUBI: Undefined behavior
// ALIVE_EXEC: Undefined behavior
