// RUN: veir-interpret %s | filecheck %s

// A pointer assembled from the low half of one stored pointer and the high
// half of another. The two objects share their high four address bytes, so
// the address is `%a`'s, and the load through it reads `%a`.
//
// LLUBI and ALIVE_EXEC: report undefined behaviour: for them each byte of a
// stored pointer remembers the pointer it came from, and bytes of two
// pointers make one with no provenance.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %b = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %sa = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %sb = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %dst = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %a) : (i64, !llvm.ptr) -> ()
    "llvm.store"(%a, %sa) : (!llvm.ptr, !llvm.ptr) -> ()
    "llvm.store"(%b, %sb) : (!llvm.ptr, !llvm.ptr) -> ()
    %sb4 = "llvm.getelementptr"(%sb, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst4 = "llvm.getelementptr"(%dst, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.intr.memcpy"(%dst, %sa, %four) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    "llvm.intr.memcpy"(%dst4, %sb4, %four) <{isVolatile = false}> : (!llvm.ptr, !llvm.ptr, i64) -> ()
    %p = "llvm.load"(%dst) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
