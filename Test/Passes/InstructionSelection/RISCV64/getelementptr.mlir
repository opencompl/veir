// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// `llvm.getelementptr` lowers to `ptr + idx * scale` for each dynamic index,
// where `scale` is the allocation size (ABI stride) of the type it steps over,
// plus the constant offset of its constant indices.

"builtin.module"() ({
    "func.func"()  <{function_type = (!llvm.ptr, i64, i32) -> (), sym_name = "foo"}> ({
    ^bb0(%p: !llvm.ptr, %i: i64, %j: i32):
        // scale 1 (i8): ptr + idx -> riscv.add
        %g1 = "llvm.getelementptr"(%p, %i) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // scale 2 (i16): (idx << 1) + ptr -> riscv.sh1add
        %g2 = "llvm.getelementptr"(%p, %i) <{elem_type = i16, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sh1add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // scale 4 (i32): (idx << 2) + ptr -> riscv.sh2add
        %g4 = "llvm.getelementptr"(%p, %i) <{elem_type = i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sh2add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // i24 has store size 3 but RV64 allocation stride 4: also riscv.sh2add
        %g24 = "llvm.getelementptr"(%p, %i) <{elem_type = i24, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sh2add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // scale 8 (i64): (idx << 3) + ptr -> riscv.sh3add
        %g8 = "llvm.getelementptr"(%p, %i) <{elem_type = i64, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sh3add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // scale 8 via array element type [8 x i8]: also riscv.sh3add
        %garr = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.array<8 x i8>, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sh3add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // scale 16 (power of two > 8): ptr + (idx << 4) -> riscv.slli + riscv.add
        %g16 = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.array<16 x i8>, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{"value" = 4 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // scale 3: ptr + idx * 3 -> riscv.li + riscv.mul + riscv.add
        %g3 = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.array<3 x i8>, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.mul"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // scale 0: a zero-sized element type also satisfies `scale &&& (scale - 1) == 0`, so it must
        // not take the power-of-two path -- `Nat.log2 0 = 0` would emit `idx << 0`, i.e. `ptr + idx`
        // instead of `ptr`. It takes the `li`/`mul` path, computing `ptr + idx * 0 = ptr`.
        %g0 = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.array<0 x i32>, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 0 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.mul"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // two dynamic indices into [9 x [9 x i8]]: strides 81 and 9
        %g2d = "llvm.getelementptr"(%p, %i, %i) <{elem_type = !llvm.array<9 x !llvm.array<9 x i8>>, rawConstantIndices = array<i32: -2147483648, -2147483648>}> : (!llvm.ptr, i64, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 81 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.mul"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.mul"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // an i32 index is sign-extended first
        %gi32 = "llvm.getelementptr"(%p, %j) <{elem_type = i32, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i32) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i32) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sextw"(%{{.*}}) : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.sh2add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // a struct field after a dynamic index: field 2 of {i8, i32, i64} is at offset 8
        %gfield = "llvm.getelementptr"(%p, %i) <{elem_type = !llvm.struct<(i8, i32, i64)>, rawConstantIndices = array<i32: -2147483648, 2>}> : (!llvm.ptr, i64) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (i64) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.slli"(%{{.*}}) <{"value" = 4 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.addi"(%{{.*}}) <{"value" = 8 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // constant indices only: a single addi
        %gconst = "llvm.getelementptr"(%p) <{elem_type = i64, rawConstantIndices = array<i32: -5>}> : (!llvm.ptr) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.addi"(%{{.*}}) <{"value" = -40 : i64}> : (!riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // a constant offset that does not fit addi's 12 bits: li + add
        %gbig = "llvm.getelementptr"(%p) <{elem_type = !llvm.array<4096 x i8>, rawConstantIndices = array<i32: 1>}> : (!llvm.ptr) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 4096 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // a zero offset: the base pointer itself
        %gzero = "llvm.getelementptr"(%p) <{elem_type = !llvm.struct<(i8, i32)>, rawConstantIndices = array<i32: 0, 0>}> : (!llvm.ptr) -> !llvm.ptr
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!llvm.ptr) -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        "test.test"(%g1) : (!llvm.ptr) -> ()
        "test.test"(%g2) : (!llvm.ptr) -> ()
        "test.test"(%g4) : (!llvm.ptr) -> ()
        "test.test"(%g24) : (!llvm.ptr) -> ()
        "test.test"(%g8) : (!llvm.ptr) -> ()
        "test.test"(%garr) : (!llvm.ptr) -> ()
        "test.test"(%g16) : (!llvm.ptr) -> ()
        "test.test"(%g3) : (!llvm.ptr) -> ()
        "test.test"(%g0) : (!llvm.ptr) -> ()
        "test.test"(%g2d) : (!llvm.ptr) -> ()
        "test.test"(%gi32) : (!llvm.ptr) -> ()
        "test.test"(%gfield) : (!llvm.ptr) -> ()
        "test.test"(%gconst) : (!llvm.ptr) -> ()
        "test.test"(%gbig) : (!llvm.ptr) -> ()
        "test.test"(%gzero) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
