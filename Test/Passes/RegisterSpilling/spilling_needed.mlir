// RUN: veir-opt %s -p='register-spilling-riscv64' | filecheck %s 

"builtin.module"() ({

  "riscv_cf.func"() <{sym_name = "arithmetic", function_type = () -> ()}> ({
    %1 = "riscv.li"() <{value = 1 : i64}> : () -> !riscv.reg
    %2 = "riscv.li"() <{value = 2 : i64}> : () -> !riscv.reg
    %3 = "riscv.li"() <{value = 3 : i64}> : () -> !riscv.reg
    %4 = "riscv.li"() <{value = 4 : i64}> : () -> !riscv.reg
    %5 = "riscv.li"() <{value = 5 : i64}> : () -> !riscv.reg
    %6 = "riscv.li"() <{value = 6 : i64}> : () -> !riscv.reg
    %7 = "riscv.li"() <{value = 7 : i64}> : () -> !riscv.reg
    %8 = "riscv.li"() <{value = 8 : i64}> : () -> !riscv.reg
    %9 = "riscv.li"() <{value = 9 : i64}> : () -> !riscv.reg
    %10 = "riscv.li"() <{value = 10 : i64}> : () -> !riscv.reg
    %11 = "riscv.li"() <{value = 11 : i64}> : () -> !riscv.reg
    %12 = "riscv.li"() <{value = 12 : i64}> : () -> !riscv.reg
    %13 = "riscv.li"() <{value = 13 : i64}> : () -> !riscv.reg
    %14 = "riscv.li"() <{value = 14 : i64}> : () -> !riscv.reg
    %15 = "riscv.li"() <{value = 15 : i64}> : () -> !riscv.reg
    %16 = "riscv.li"() <{value = 16 : i64}> : () -> !riscv.reg
    %17 = "riscv.li"() <{value = 17 : i64}> : () -> !riscv.reg
    %18 = "riscv.li"() <{value = 18 : i64}> : () -> !riscv.reg
    %19 = "riscv.li"() <{value = 19 : i64}> : () -> !riscv.reg
    %20 = "riscv.li"() <{value = 20 : i64}> : () -> !riscv.reg
    %21 = "riscv.li"() <{value = 21 : i64}> : () -> !riscv.reg
    %22 = "riscv.li"() <{value = 22 : i64}> : () -> !riscv.reg
    %23 = "riscv.li"() <{value = 23 : i64}> : () -> !riscv.reg
    %24 = "riscv.li"() <{value = 24 : i64}> : () -> !riscv.reg
    %25 = "riscv.li"() <{value = 25 : i64}> : () -> !riscv.reg
    %26 = "riscv.li"() <{value = 26 : i64}> : () -> !riscv.reg
    %27 = "riscv.li"() <{value = 27 : i64}> : () -> !riscv.reg
    %28 = "riscv.li"() <{value = 28 : i64}> : () -> !riscv.reg
    %29 = "riscv.li"() <{value = 29 : i64}> : () -> !riscv.reg
    %30 = "riscv.li"() <{value = 30 : i64}> : () -> !riscv.reg
    %31 = "riscv.li"() <{value = 31 : i64}> : () -> !riscv.reg
    %32 = "riscv.li"() <{value = 32 : i64}> : () -> !riscv.reg
    %33 = "riscv.li"() <{value = 33 : i64}> : () -> !riscv.reg

    
    %s1 = "riscv.add"(%1, %2) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s2 = "riscv.add"(%s1, %3) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s3 = "riscv.add"(%s2, %4) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s4 = "riscv.add"(%s3, %5) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s5 = "riscv.add"(%s4, %6) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s6 = "riscv.add"(%s5, %7) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s7 = "riscv.add"(%s6, %8) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s8 = "riscv.add"(%s7, %9) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s9 = "riscv.add"(%s8, %10) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s10 = "riscv.add"(%s9, %11) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s11 = "riscv.add"(%s10, %12) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s12 = "riscv.add"(%s11, %13) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s13 = "riscv.add"(%s12, %14) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s14 = "riscv.add"(%s13, %15) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s15 = "riscv.add"(%s14, %16) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s16 = "riscv.add"(%s15, %17) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s17 = "riscv.add"(%s16, %18) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s18 = "riscv.add"(%s17, %19) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s19 = "riscv.add"(%s18, %20) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s20 = "riscv.add"(%s19, %21) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s21 = "riscv.add"(%s20, %22) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s22 = "riscv.add"(%s21, %23) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s23 = "riscv.add"(%s22, %24) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s24 = "riscv.add"(%s23, %25) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s25 = "riscv.add"(%s24, %26) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s26 = "riscv.add"(%s25, %27) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s27 = "riscv.add"(%s26, %28) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s28 = "riscv.add"(%s27, %29) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s29 = "riscv.add"(%s28, %30) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s30 = "riscv.add"(%s29, %31) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s31 = "riscv.add"(%s30, %32) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %s32 = "riscv.add"(%s31, %33) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "riscv_cf.return"() : () -> ()
  }) : () -> ()

}) : () -> ()


// CHECK-LABEL: "sym_name" = "arithmetic"
// CHECK-NEXT:  ^{{[^ ]+}}():

// The first 28 values fit in registers.
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 1 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 2 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 3 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 4 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 5 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 6 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 7 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 9 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 10 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 11 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 12 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 13 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 14 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 15 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 16 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 17 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 18 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 19 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 20 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 21 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 22 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 23 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 24 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 25 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 26 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 27 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 28 : i64}> : () -> !riscv.reg

// Each further value needs a register, so one loaded value is stored to a new slot first.
// CHECK-NEXT:  [[SLOT:%[^ ]+]] = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  "riscv.sd"(%{{[^ ]+}}, [[SLOT]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 29 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  [[SLOT:%[^ ]+]] = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  "riscv.sd"(%{{[^ ]+}}, [[SLOT]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 30 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  [[SLOT:%[^ ]+]] = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  "riscv.sd"(%{{[^ ]+}}, [[SLOT]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 31 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  [[SLOT:%[^ ]+]] = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  "riscv.sd"(%{{[^ ]+}}, [[SLOT]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 32 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  [[SLOT:%[^ ]+]] = "riscv_stack.alloca"() <{"alignment" = 8 : i64, "size" = 8 : i64}> : () -> !riscv.reg
// CHECK-NEXT:  "riscv.sd"(%{{[^ ]+}}, [[SLOT]]) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.li"() <{"value" = 33 : i64}> : () -> !riscv.reg

// Every stored value is reloaded right before the add that uses it. Where in the add
// chain each reload lands depends on which value was evicted, so these allow gaps.
// CHECK:       [[R:%[^ ]+]] = "riscv.ld"(%{{[^ ]+}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"({{.*}}[[R]]{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:       [[R:%[^ ]+]] = "riscv.ld"(%{{[^ ]+}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"({{.*}}[[R]]{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:       [[R:%[^ ]+]] = "riscv.ld"(%{{[^ ]+}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"({{.*}}[[R]]{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:       [[R:%[^ ]+]] = "riscv.ld"(%{{[^ ]+}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"({{.*}}[[R]]{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CHECK:       [[R:%[^ ]+]] = "riscv.ld"(%{{[^ ]+}}) <{"value" = 0 : i64}> : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT:  %{{[^ ]+}} = "riscv.add"({{.*}}[[R]]{{.*}}) : (!riscv.reg, !riscv.reg) -> !riscv.reg

// CHECK:       "riscv_cf.return"() : () -> ()
