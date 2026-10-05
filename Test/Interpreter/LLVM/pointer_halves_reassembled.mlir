// RUN: veir-interpret %s | filecheck %s
// RUN: ALIVE_EXEC

// A stored pointer read back as two `i32` halves, joined with shifts and cast
// back to a pointer, reaches its object: the bytes carry the address.
//
// LLUBI: reports undefined behaviour: the pointer cast back from the halves
// has no provenance for it.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %c32 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %a) : (i64, !llvm.ptr) -> ()
    "llvm.store"(%a, %slot) : (!llvm.ptr, !llvm.ptr) -> ()
    %slot4 = "llvm.getelementptr"(%slot, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %lo = "llvm.load"(%slot) : (!llvm.ptr) -> i32
    %hi = "llvm.load"(%slot4) : (!llvm.ptr) -> i32
    %lo64 = "llvm.zext"(%lo) : (i32) -> i64
    %hi64 = "llvm.zext"(%hi) : (i32) -> i64
    %hish = "llvm.shl"(%hi64, %c32) : (i64, i64) -> i64
    %addr = "llvm.or"(%lo64, %hish) : (i64, i64) -> i64
    %p = "llvm.inttoptr"(%addr) : (i64) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
