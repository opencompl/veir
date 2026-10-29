// RUN: veir-interpret %s | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p=llvm-to-gmir,legalize-riscv64 > %t.gmir && veir-interpret %t.gmir | filecheck %s --check-prefix=SRC
// RUN: veir-opt %s --print-op-generic -p='canonicalize{sccp=false},instcombine,canonicalize{sccp=false},cse,dce,riscv' > %t
// RUN: veir-interpret %t >> %t
// RUN: filecheck %s < %t

// Unlike in `saturating_i64_exec.mlir`, the add and sub are lowered with an overflowing operation
// and a select, as min and max are only legal for `i64`. Each `i32` operation saturates in one case
// and not in the other.

"builtin.module"() ({
  "func.func"() <{sym_name = "main", function_type = () -> (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i8, i8, i8, i8, i16, i16)}> ({
    %max32 = "llvm.mlir.constant"() <{value = 2147483647 : i32}> : () -> i32
    %min32 = "llvm.mlir.constant"() <{value = -2147483648 : i32}> : () -> i32
    %one32 = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %two32 = "llvm.mlir.constant"() <{value = 2 : i32}> : () -> i32
    %neg32 = "llvm.mlir.constant"() <{value = -3 : i32}> : () -> i32
    %big32 = "llvm.mlir.constant"() <{value = 1073741824 : i32}> : () -> i32
    %uadd_sat = "llvm.intr.uadd.sat"(%neg32, %max32) : (i32, i32) -> i32
    %uadd = "llvm.intr.uadd.sat"(%max32, %one32) : (i32, i32) -> i32
    %usub_sat = "llvm.intr.usub.sat"(%one32, %two32) : (i32, i32) -> i32
    %usub = "llvm.intr.usub.sat"(%neg32, %one32) : (i32, i32) -> i32
    %sadd_sat = "llvm.intr.sadd.sat"(%max32, %one32) : (i32, i32) -> i32
    %sadd = "llvm.intr.sadd.sat"(%min32, %max32) : (i32, i32) -> i32
    %ssub_sat = "llvm.intr.ssub.sat"(%min32, %one32) : (i32, i32) -> i32
    %ssub = "llvm.intr.ssub.sat"(%neg32, %one32) : (i32, i32) -> i32
    %sshl_sat = "llvm.intr.sshl.sat"(%big32, %two32) : (i32, i32) -> i32
    %sshl = "llvm.intr.sshl.sat"(%neg32, %two32) : (i32, i32) -> i32
    %ushl_sat = "llvm.intr.ushl.sat"(%big32, %two32) : (i32, i32) -> i32
    %ushl = "llvm.intr.ushl.sat"(%big32, %one32) : (i32, i32) -> i32
    %max8 = "llvm.mlir.constant"() <{value = 127 : i8}> : () -> i8
    %one8 = "llvm.mlir.constant"() <{value = 1 : i8}> : () -> i8
    %neg8 = "llvm.mlir.constant"() <{value = -2 : i8}> : () -> i8
    %uadd8 = "llvm.intr.uadd.sat"(%neg8, %neg8) : (i8, i8) -> i8
    %sadd8 = "llvm.intr.sadd.sat"(%max8, %one8) : (i8, i8) -> i8
    %ssub8 = "llvm.intr.ssub.sat"(%neg8, %max8) : (i8, i8) -> i8
    %sshl8 = "llvm.intr.sshl.sat"(%max8, %one8) : (i8, i8) -> i8
    %a16 = "llvm.mlir.constant"() <{value = 30000 : i16}> : () -> i16
    %neg16 = "llvm.mlir.constant"() <{value = -2 : i16}> : () -> i16
    %one16 = "llvm.mlir.constant"() <{value = 1 : i16}> : () -> i16
    %usub16 = "llvm.intr.usub.sat"(%a16, %neg16) : (i16, i16) -> i16
    %ushl16 = "llvm.intr.ushl.sat"(%a16, %one16) : (i16, i16) -> i16
    "func.return"(%uadd_sat, %uadd, %usub_sat, %usub, %sadd_sat, %sadd, %ssub_sat, %ssub, %sshl_sat, %sshl, %ushl_sat, %ushl, %uadd8, %sadd8, %ssub8, %sshl8, %usub16, %ushl16) : (i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i32, i8, i8, i8, i8, i16, i16) -> ()
  }) : () -> ()
}) : () -> ()

// SRC:       Program output: #[0xffffffff#32, 0x80000000#32, 0x00000000#32, 0xfffffffc#32, 0x7fffffff#32, 0xffffffff#32, 0x80000000#32, 0xfffffffc#32, 0x7fffffff#32, 0xfffffff4#32, 0xffffffff#32, 0x80000000#32, 0xff#8, 0x7f#8, 0x80#8, 0x7f#8, 0x0000#16, 0xea60#16]
// CHECK-NOT: "llvm.intr
// CHECK-NOT: "gmir.
// CHECK:     "riscv.czeroeqz"
// CHECK:     Program output: #[0xffffffff#32, 0x80000000#32, 0x00000000#32, 0xfffffffc#32, 0x7fffffff#32, 0xffffffff#32, 0x80000000#32, 0xfffffffc#32, 0x7fffffff#32, 0xfffffff4#32, 0xffffffff#32, 0x80000000#32, 0xff#8, 0x7f#8, 0x80#8, 0x7f#8, 0x0000#16, 0xea60#16]
