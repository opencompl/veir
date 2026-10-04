// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

// `llvm.mlir.addressof` lowers to `riscv.la`, printed as `PseudoLLA`. Each
// global becomes a stub IR global for `llc` to emit: an integer or string
// `value` is its initializer, and a global without one is an external
// declaration.

"builtin.module"() ({
  "llvm.mlir.global"() <{addr_space = 0 : i32, alignment = 4 : i64, global_type = i32, linkage = #llvm.linkage<external>, sym_name = "g", value = 41 : i32}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, constant, global_type = !llvm.array<3 x i8>, linkage = #llvm.linkage<internal>, sym_name = "s", value = "hi\00"}> ({
  }) : () -> ()
  "llvm.mlir.global"() <{addr_space = 0 : i32, global_type = i64, linkage = #llvm.linkage<external>, sym_name = "e"}> ({
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i32 ()>, sym_name = "increment"}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i32}> : () -> i32
    %g = "llvm.mlir.addressof"() <{global_name = @g}> : () -> !llvm.ptr
    %old = "llvm.load"(%g) : (!llvm.ptr) -> i32
    %new = "llvm.add"(%old, %one) : (i32, i32) -> i32
    "llvm.store"(%new, %g) : (i32, !llvm.ptr) -> ()
    "llvm.return"(%new) : (i32) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "second_char"}> ({
    %one = "llvm.mlir.constant"() <{value = 1 : i64}> : () -> i64
    %s = "llvm.mlir.addressof"() <{global_name = @s}> : () -> !llvm.ptr
    %s1 = "llvm.getelementptr"(%s, %one) <{elem_type = i8, rawConstantIndices = array<i32: -2147483648>}> : (!llvm.ptr, i64) -> !llvm.ptr
    %c = "llvm.load"(%s1) : (!llvm.ptr) -> i8
    %r = "llvm.zext"(%c) : (i8) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{function_type = !llvm.func<i64 ()>, sym_name = "load_external"}> ({
    %e = "llvm.mlir.addressof"() <{global_name = @e}> : () -> !llvm.ptr
    %r = "llvm.load"(%e) : (!llvm.ptr) -> i64
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:          @g = global i32 41, align 4
// CHECK-NEXT:     @s = internal constant [3 x i8] c"hi\00"
// CHECK-NEXT:     @e = external global i64
// CHECK-NOT:      declare

// CHECK-LABEL:  name: increment
// CHECK:          [[G:%v[0-9]+]]:gpr = PseudoLLA @g
// CHECK-NEXT:     [[OLD:%v[0-9]+]]:gpr = LW [[G]], 0
// CHECK:          SW {{%v[0-9]+}}, [[G]], 0

// CHECK-LABEL:  name: second_char
// CHECK:          [[S:%v[0-9]+]]:gpr = PseudoLLA @s
// CHECK-NEXT:     {{%v[0-9]+}}:gpr = LB{{U?}} [[S]], 1

// CHECK-LABEL:  name: load_external
// CHECK:          [[E:%v[0-9]+]]:gpr = PseudoLLA @e
// CHECK-NEXT:     {{%v[0-9]+}}:gpr = LD [[E]], 0
