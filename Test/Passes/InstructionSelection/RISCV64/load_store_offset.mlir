// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// A `llvm.getelementptr` with a constant index is absorbed into the signed
// 12-bit offset field of the load or store that uses it, mirroring the
// `isBaseWithConstantOffset` case of LLVM's `SelectAddrRegImm`. The gep itself
// becomes dead and is erased, so no address arithmetic remains.

"builtin.module"() ({
    // i64 element, index 4 -> byte offset 32.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "fold_ld"}> ({
    ^bb0(%p: !llvm.ptr):
        %i = "llvm.mlir.constant"() <{value = 4 : i64}> : () -> i64
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %v = "llvm.load"(%g) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.ld"({{.*}}) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i64
        "test.test"(%v) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // A negative index gives a negative offset: i32 element, index -1 -> -4.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "fold_negative"}> ({
    ^bb0(%p: !llvm.ptr):
        %i = "llvm.mlir.constant"() <{value = -1 : i64}> : () -> i64
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %v = "llvm.load"(%g) : (!llvm.ptr) -> i32
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.lw"({{.*}}) <{"value" = -4 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i32
        "test.test"(%v) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // Folding uses allocation stride, not store size: i33 has store size 5 but
    // RV64 allocation stride 8, so index 2 gives byte offset 16.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "fold_i33_stride"}> ({
    ^bb0(%p: !llvm.ptr):
        %i = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = i33, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %v = "llvm.load"(%g) : (!llvm.ptr) -> i32
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.lw"({{.*}}) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!riscv.reg) -> i32
        "test.test"(%v) : (i32) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // Stores fold the same way: i8 element, index 7 -> byte offset 7.
    "func.func"()  <{function_type = (!llvm.ptr, i8) -> (), sym_name = "fold_sb"}> ({
    ^bb0(%p: !llvm.ptr, %x: i8):
        %i = "llvm.mlir.constant"() <{value = 7 : i64}> : () -> i64
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        "llvm.store"(%x, %g) : (i8, !llvm.ptr) -> ()
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (i8) -> !riscv.reg
        // CHECK-NEXT: "riscv.sb"({{.*}}, {{.*}}) <{"value" = 7 : i64}> : (!riscv.reg, !riscv.reg) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // The extreme in-range offsets still fold: 2047 and -2048 with an i8 element.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "fold_boundaries"}> ({
    ^bb0(%p: !llvm.ptr):
        %hi = "llvm.mlir.constant"() <{value = 2047 : i64}> : () -> i64
        %ghi = "llvm.getelementptr"(%p, %hi) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %vhi = "llvm.load"(%ghi) : (!llvm.ptr) -> i8
        // CHECK:      {{.*}} = "riscv.lb"({{.*}}) <{"value" = 2047 : i64}> : (!riscv.reg) -> !riscv.reg
        "test.test"(%vhi) : (i8) -> ()
        %lo = "llvm.mlir.constant"() <{value = -2048 : i64}> : () -> i64
        %glo = "llvm.getelementptr"(%p, %lo) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %vlo = "llvm.load"(%glo) : (!llvm.ptr) -> i8
        // CHECK:      {{.*}} = "riscv.lb"({{.*}}) <{"value" = -2048 : i64}> : (!riscv.reg) -> !riscv.reg
        "test.test"(%vlo) : (i8) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // The range is checked on the *scaled* offset: the index 1000 fits a signed
    // 12-bit field but 1000 * 8 = 8000 does not, so the address is computed into
    // a register by the `getelementptr` lowering and the load keeps offset 0.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "nofold_scaled_out_of_range"}> ({
    ^bb0(%p: !llvm.ptr):
        %i = "llvm.mlir.constant"() <{value = 1000 : i64}> : () -> i64
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %v = "llvm.load"(%g) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "riscv.li"() <{"value" = 1000 : i64}> : () -> !riscv.reg
        // CHECK:      {{.*}} = "riscv.sh3add"({{.*}}, {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:      {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        "test.test"(%v) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // A non-constant index has no offset to fold.
    "func.func"()  <{function_type = (!llvm.ptr, i64) -> (), sym_name = "nofold_dynamic"}> ({
    ^bb0(%p: !llvm.ptr, %i: i64):
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %v = "llvm.load"(%g) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "riscv.sh3add"({{.*}}, {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:      {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        "test.test"(%v) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // Folding does not depend on the gep having a single user: as in LLVM, the
    // load takes the offset and the gep is still selected for its other user,
    // duplicating the address arithmetic.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "fold_multi_use"}> ({
    ^bb0(%p: !llvm.ptr):
        %i = "llvm.mlir.constant"() <{value = 2 : i64}> : () -> i64
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %v = "llvm.load"(%g) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "riscv.sh3add"({{.*}}, {{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK:      {{.*}} = "riscv.ld"({{.*}}) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
        "test.test"(%v) : (i64) -> ()
        "test.test"(%g) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()

    // Zero-sized element types scale to offset 0, which folds and drops the gep.
    "func.func"()  <{function_type = (!llvm.ptr) -> (), sym_name = "fold_zero_sized_elem"}> ({
    ^bb0(%p: !llvm.ptr):
        %i = "llvm.mlir.constant"() <{value = 5 : i64}> : () -> i64
        %g = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.array<0 x i32>, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        %v = "llvm.load"(%g) : (!llvm.ptr) -> i64
        // CHECK:      {{.*}} = "builtin.unrealized_conversion_cast"({{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: {{.*}} = "riscv.ld"({{.*}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
        "test.test"(%v) : (i64) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
