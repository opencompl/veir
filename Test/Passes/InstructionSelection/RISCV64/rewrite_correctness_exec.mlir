// RUN: veir-interpret %s | filecheck %s --check-prefix=RESULT
// RUN: veir-opt %s -p=isel-riscv64 > %t
// RUN: veir-interpret %t | filecheck %s --check-prefix=RESULT
// RUN: filecheck %s --check-prefix=ISEL --input-file=%t

// Decode attributes at their own widths, including zero-extension of i1.
// Exercise both constant rotates, both folded memory operations, and both
// constant-index and dynamic-index GEPs whose ABI strides include tail padding.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i64, i64, i64, i32, i32, i8, i8, i8, i8)}> ({
    %signed = "llvm.mlir.constant"() <{value = 255 : i8}> : () -> i64
    %boolean = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i64
    %signed32 = "llvm.mlir.constant"() <{value = 4294967295 : i32}> : () -> i64
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %right = "llvm.intr.fshr"(%one, %one, %boolean) : (i64, i64, i64) -> i64
    %left = "llvm.intr.fshl"(%one, %one, %boolean) : (i64, i64, i64) -> i64
    %one32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %boolean32 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i32
    %right32 = "llvm.intr.fshr"(%one32, %one32, %boolean32) : (i32, i32, i32) -> i32
    %left32 = "llvm.intr.fshl"(%one32, %one32, %boolean32) : (i32, i32, i32) -> i32

    %size = "llvm.mlir.constant"() <{value = 16 : i64}> : () -> i64
    %mem = "llvm.alloca"(%size) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %three = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %four = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
    %five = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
    %base = "llvm.getelementptr"(%mem, %four) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %negative = "llvm.getelementptr"(%base, %signed) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %v42 = "llvm.mlir.constant"() <{value = 42 : i8}> : () -> i8
    "llvm.store"(%v42, %negative) : (i8, !llvm.ptr) -> ()
    %at3 = "llvm.getelementptr"(%mem, %three) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %stored = "llvm.load"(%at3) : (!llvm.ptr) -> i8

    %v99 = "llvm.mlir.constant"() <{value = 99 : i8}> : () -> i8
    "llvm.store"(%v99, %base) : (i8, !llvm.ptr) -> ()
    %v43 = "llvm.mlir.constant"() <{value = 43 : i8}> : () -> i8
    %at5 = "llvm.getelementptr"(%mem, %five) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    "llvm.store"(%v43, %at5) : (i8, !llvm.ptr) -> ()
    %positive = "llvm.getelementptr"(%base, %boolean) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %loaded = "llvm.load"(%positive) : (!llvm.ptr) -> i8

    %i24const = "llvm.getelementptr"(%mem, %one) <{elem_type = i24, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %constantStride = "llvm.load"(%i24const) : (!llvm.ptr) -> i8
    %zero = "llvm.mlir.constant"() <{value = 0 : i64}> : () -> i64
    %dynamic = "llvm.add"(%one, %zero) : (i64, i64) -> i64
    %i24dynamic = "llvm.getelementptr"(%mem, %dynamic) <{elem_type = i24, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %dynamicStride = "llvm.load"(%i24dynamic) : (!llvm.ptr) -> i8
    "func.return"(%signed, %boolean, %signed32, %right, %left, %right32, %left32, %stored, %loaded, %constantStride, %dynamicStride) : (i64, i64, i64, i64, i64, i32, i32, i8, i8, i8, i8) -> ()
  }) : () -> ()
}) : () -> ()

// RESULT: Program output: #[0xffffffffffffffff#64, 0x0000000000000001#64, 0xffffffffffffffff#64, 0x8000000000000000#64, 0x0000000000000002#64, 0x80000000#32, 0x00000002#32, 0x2a#8, 0x2b#8, 0x63#8, 0x63#8]
// ISEL: "riscv.rori"({{.*}}) <{"value" = 1 : i64}>
// ISEL: "riscv.rori"({{.*}}) <{"value" = 63 : i64}>
// ISEL: "riscv.roriw"({{.*}}) <{"value" = 1 : i64}>
// ISEL: "riscv.roriw"({{.*}}) <{"value" = 31 : i64}>
// ISEL: "riscv.sb"({{.*}}) <{"value" = -1 : i64}>
// ISEL: "riscv.lb"({{.*}}) <{"value" = 1 : i64}>
// ISEL: "riscv.lb"({{.*}}) <{"value" = 4 : i64}>
// ISEL: "riscv.sh2add"({{.*}}, {{.*}})
// ISEL: "riscv.lb"({{.*}}) <{"value" = 0 : i64}>
