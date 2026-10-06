// RUN: veir-interpret %s | filecheck %s

// A pointer's address split into two `i32` halves, stored side by side and
// loaded back as a pointer reaches the object.
//
// LLUBI and ALIVE_EXEC: report undefined behaviour: for them a pointer loaded
// from bytes an integer wrote has no provenance.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 ()>}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %v = "llvm.mlir.constant"() <{value = 42 : i64}> : () -> i64
    %c32 = "llvm.mlir.constant"() <{value = 32 : i64}> : () -> i64
    %a = "llvm.alloca"(%one) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %dst = "llvm.alloca"(%one) <{elem_type = !llvm.ptr}> : (i64) -> !llvm.ptr
    "llvm.store"(%v, %a) : (i64, !llvm.ptr) -> ()
    %addr = "llvm.ptrtoint"(%a) : (!llvm.ptr) -> i64
    %lo = "llvm.trunc"(%addr) : (i64) -> i32
    %hish = "llvm.lshr"(%addr, %c32) : (i64, i64) -> i64
    %hi = "llvm.trunc"(%hish) : (i64) -> i32
    %dst4 = "llvm.getelementptr"(%dst, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%lo, %dst) : (i32, !llvm.ptr) -> ()
    "llvm.store"(%hi, %dst4) : (i32, !llvm.ptr) -> ()
    %p = "llvm.load"(%dst) : (!llvm.ptr) -> !llvm.ptr
    %r = "llvm.load"(%p) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: Program output: #[0x000000000000002a#64]
