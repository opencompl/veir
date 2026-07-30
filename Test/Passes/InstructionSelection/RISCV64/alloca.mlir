// RUN: veir-opt %s -p=isel-riscv64 | filecheck %s

// An entry-block `llvm.alloca` with a constant element count lowers to a
// `riscv_stack.alloca` stack object of `sizeof(elem_type) * count` bytes, plus a
// cast of its address back to `!llvm.ptr`. When the `alignment` property is `0`
// (left to the target) the natural alignment of the element type is used.

"builtin.module"() ({
    "func.func"()  <{function_type = () -> (), sym_name = "foo"}> ({
    ^bb0():
        %c1 = "llvm.mlir.constant"() <{ "value" = 1 : i64 }> : () -> i64
        %c2 = "llvm.mlir.constant"() <{ "value" = 2 : i64 }> : () -> i64
        %c8 = "llvm.mlir.constant"() <{ "value" = 8 : i64 }> : () -> i64

        // 8 x i64 = 64 bytes, natural alignment 8
        %a = "llvm.alloca"(%c8) <{ elem_type = i64 }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 64 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // 1 x i8 = 1 byte, natural alignment 1
        %b = "llvm.alloca"(%c1) <{ elem_type = i8 }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 1 : i64, "size" = 1 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // 8 x i32 = 32 bytes, natural alignment 4
        %c = "llvm.alloca"(%c8) <{ elem_type = i32 }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 4 : i64, "size" = 32 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // An explicit alignment overrides the natural one.
        %d = "llvm.alloca"(%c1) <{ elem_type = i32, alignment = 16 : i64 }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 16 : i64, "size" = 4 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // An aggregate element type: 8 x [3 x i16] = 48 bytes, aligned like the element, 2.
        %e = "llvm.alloca"(%c8) <{ elem_type = !llvm.array<3 x i16> }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 2 : i64, "size" = 48 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // A pointer element type: 1 x ptr = 8 bytes, alignment 8.
        %f = "llvm.alloca"(%c1) <{ elem_type = !llvm.ptr }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // Allocation size includes ABI tail padding: i24 has store size 3,
        // alignment 4, and allocation stride 4, so two elements need 8 bytes.
        %h = "llvm.alloca"(%c2) <{ elem_type = i24 }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 4 : i64, "size" = 8 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // RV64 gives i128 a 16-byte ABI alignment.
        %i = "llvm.alloca"(%c1) <{ elem_type = i128 }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 16 : i64, "size" = 16 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr

        // The element count is read from the defining `llvm.mlir.constant`, so the alloca
        // must be selected before that constant is rewritten to a `riscv.li`. Here the
        // constant has another use and so survives selection in its own right.
        %g = "llvm.alloca"(%c8) <{ elem_type = i16 }> : (i64) -> !llvm.ptr
        // CHECK:      %{{.*}} = "riscv_stack.alloca"() <{"alignment" = 2 : i64, "size" = 16 : i64}> : () -> !riscv.reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!riscv.reg) -> !llvm.ptr
        %sum = "llvm.add"(%c8, %c8) : (i64, i64) -> i64

        // No `llvm.alloca` survives.
        // CHECK-NOT: llvm.alloca

        "test.test"(%sum) : (i64) -> ()
        "test.test"(%g) : (!llvm.ptr) -> ()
        "test.test"(%a) : (!llvm.ptr) -> ()
        "test.test"(%b) : (!llvm.ptr) -> ()
        "test.test"(%c) : (!llvm.ptr) -> ()
        "test.test"(%d) : (!llvm.ptr) -> ()
        "test.test"(%e) : (!llvm.ptr) -> ()
        "test.test"(%f) : (!llvm.ptr) -> ()
        "test.test"(%h) : (!llvm.ptr) -> ()
        "test.test"(%i) : (!llvm.ptr) -> ()
        "func.return"() : () -> ()
    }) : () -> ()
}) : () -> ()
