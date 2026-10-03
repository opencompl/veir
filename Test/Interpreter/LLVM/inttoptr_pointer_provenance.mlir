// RUN: veir-interpret %s | filecheck %s

// The walk of `bitcast_pointer_provenance.mlir` through `llvm.ptrtoint` and
// `llvm.inttoptr` instead of a bitcast. The pointer that comes back is pinned
// to the object its address lies in, which is `%q`, so walking sixteen bytes
// back leaves that object and the load is undefined behaviour.
//
// LLUBI and ALIVE_EXEC: both read 42 instead. For them an integer carries an
// address and nothing else, so the pointer it is cast back to reaches
// whichever object the address lies in at each access, and the walk returns
// to `%p`.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %k = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %mk = "llvm.mlir.constant"() <{value = -16 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %p = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %q = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %p) : (i64, !llvm.ptr) -> ()
    %past = "llvm.getelementptr"(%p, %k) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %addr = "llvm.ptrtoint"(%past) : (!llvm.ptr) -> i64
    %same = "llvm.inttoptr"(%addr) : (i64) -> !llvm.ptr
    %back = "llvm.getelementptr"(%same, %mk) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %res = "llvm.load"(%back) : (!llvm.ptr) -> i64
    "llvm.return"(%res) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Undefined behavior
