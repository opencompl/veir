// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t.gmir && veir-interpret %t.gmir | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

// The operands are loaded from stack slots so that the combiner does not fold the min/max away.
"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i64, i64, i32, i32, i32, i32, i8, i8, i64, i32, i8)}> ({
    %n = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    // The operands are ordered differently as signed and as unsigned values.
    %neg64_slot = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %neg64_c = "llvm.mlir.constant"() <{value = -2 : i64}> : () -> i64
    "llvm.store"(%neg64_c, %neg64_slot) : (i64, !llvm.ptr) -> ()
    %neg64 = "llvm.load"(%neg64_slot) : (!llvm.ptr) -> i64
    %pos64 = "llvm.mlir.constant"() <{value = 3 : i64}> : () -> i64
    %neg32_slot = "llvm.alloca"(%n) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %neg32_c = "llvm.mlir.constant"() <{value = -2 : i32}> : () -> i32
    "llvm.store"(%neg32_c, %neg32_slot) : (i32, !llvm.ptr) -> ()
    %neg32 = "llvm.load"(%neg32_slot) : (!llvm.ptr) -> i32
    %pos32 = "llvm.mlir.constant"() <{value = 3 : i32}> : () -> i32
    %neg8_slot = "llvm.alloca"(%n) <{elem_type = i8}> : (i64) -> !llvm.ptr
    %neg8_c = "llvm.mlir.constant"() <{value = -2 : i8}> : () -> i8
    "llvm.store"(%neg8_c, %neg8_slot) : (i8, !llvm.ptr) -> ()
    %neg8 = "llvm.load"(%neg8_slot) : (!llvm.ptr) -> i8
    %pos8 = "llvm.mlir.constant"() <{value = 3 : i8}> : () -> i8
    %min64_slot = "llvm.alloca"(%n) <{elem_type = i64}> : (i64) -> !llvm.ptr
    %min64_c = "llvm.mlir.constant"() <{value = -9223372036854775808 : i64}> : () -> i64
    "llvm.store"(%min64_c, %min64_slot) : (i64, !llvm.ptr) -> ()
    %min64 = "llvm.load"(%min64_slot) : (!llvm.ptr) -> i64
    %min32_slot = "llvm.alloca"(%n) <{elem_type = i32}> : (i64) -> !llvm.ptr
    %min32_c = "llvm.mlir.constant"() <{value = -2147483648 : i32}> : () -> i32
    "llvm.store"(%min32_c, %min32_slot) : (i32, !llvm.ptr) -> ()
    %min32 = "llvm.load"(%min32_slot) : (!llvm.ptr) -> i32
    %smax64 = "llvm.intr.smax"(%neg64, %pos64) : (i64, i64) -> i64
    %umax64 = "llvm.intr.umax"(%neg64, %pos64) : (i64, i64) -> i64
    %smax32 = "llvm.intr.smax"(%neg32, %pos32) : (i32, i32) -> i32
    %smin32 = "llvm.intr.smin"(%neg32, %pos32) : (i32, i32) -> i32
    %umax32 = "llvm.intr.umax"(%neg32, %pos32) : (i32, i32) -> i32
    %umin32 = "llvm.intr.umin"(%neg32, %pos32) : (i32, i32) -> i32
    %smin8 = "llvm.intr.smin"(%neg8, %pos8) : (i8, i8) -> i8
    %umin8 = "llvm.intr.umin"(%neg8, %pos8) : (i8, i8) -> i8
    // The absolute value of the minimum value is the minimum value.
    %abs64 = "llvm.intr.abs"(%min64) <{is_int_min_poison = false}> : (i64) -> i64
    %abs32 = "llvm.intr.abs"(%min32) <{is_int_min_poison = false}> : (i32) -> i32
    %abs8 = "llvm.intr.abs"(%neg8) <{is_int_min_poison = false}> : (i8) -> i8
    "func.return"(%smax64, %umax64, %smax32, %smin32, %umax32, %umin32, %smin8, %umin8, %abs64, %abs32, %abs8) : (i64, i64, i32, i32, i32, i32, i8, i8, i64, i32, i8) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:   Program output: #[0x0000000000000003#64, 0xfffffffffffffffe#64, 0x00000003#32, 0xfffffffe#32, 0xfffffffe#32, 0x00000003#32, 0xfe#8, 0x03#8, 0x8000000000000000#64, 0x80000000#32, 0x02#8]
// CHECK:    "riscv.max"
// CHECK:    "riscv.maxu"
// CHECK:    "riscv.max"
// CHECK:    "riscv.min"
// CHECK:    "riscv.maxu"
// CHECK:    "riscv.minu"
// CHECK:    "riscv.min"
// CHECK:    "riscv.minu"
// CHECK:    "riscv.max"
// CHECK:    "riscv.max"
// CHECK:    "riscv.max"
// CHECK:    Program output: #[0x0000000000000003#64, 0xfffffffffffffffe#64, 0x00000003#32, 0xfffffffe#32, 0xfffffffe#32, 0x00000003#32, 0xfe#8, 0x03#8, 0x8000000000000000#64, 0x80000000#32, 0x02#8]
