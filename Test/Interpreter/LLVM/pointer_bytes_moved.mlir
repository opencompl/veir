// RUN: veir-interpret %s | filecheck %s

// A stored pointer moved byte by byte through `b8` registers, each byte
// stored where it came from, is the same pointer at the destination.
//
// LLUBI: cannot read this test: llubi crashes on a byte-typed value that
// holds pointer bits.
//
// ALIVE_EXEC: cannot read this test: it has no `b8` type.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %c2 = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
    %c3 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %c4 = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %c5 = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %c6 = "llvm.mlir.constant"() <{value = 6 : i64}> : () -> i64
    %c7 = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %slot = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    %dst = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %a) : (i64, !llvm.ptr) -> ()
    "llvm.store"(%a, %slot) : (!llvm.ptr, !llvm.ptr) -> ()
    %b0 = "llvm.load"(%slot) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b0, %dst) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %slot1 = "llvm.getelementptr"(%slot, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst1 = "llvm.getelementptr"(%dst, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %b1 = "llvm.load"(%slot1) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b1, %dst1) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %slot2 = "llvm.getelementptr"(%slot, %c2) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst2 = "llvm.getelementptr"(%dst, %c2) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %b2 = "llvm.load"(%slot2) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b2, %dst2) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %slot3 = "llvm.getelementptr"(%slot, %c3) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst3 = "llvm.getelementptr"(%dst, %c3) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %b3 = "llvm.load"(%slot3) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b3, %dst3) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %slot4 = "llvm.getelementptr"(%slot, %c4) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst4 = "llvm.getelementptr"(%dst, %c4) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %b4 = "llvm.load"(%slot4) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b4, %dst4) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %slot5 = "llvm.getelementptr"(%slot, %c5) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst5 = "llvm.getelementptr"(%dst, %c5) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %b5 = "llvm.load"(%slot5) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b5, %dst5) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %slot6 = "llvm.getelementptr"(%slot, %c6) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst6 = "llvm.getelementptr"(%dst, %c6) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %b6 = "llvm.load"(%slot6) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b6, %dst6) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %slot7 = "llvm.getelementptr"(%slot, %c7) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dst7 = "llvm.getelementptr"(%dst, %c7) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %b7 = "llvm.load"(%slot7) : (!llvm.ptr) -> !llvm.byte<8>
    "llvm.store"(%b7, %dst7) : (!llvm.byte<8>, !llvm.ptr) -> ()
    %p = "llvm.load"(%dst) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
