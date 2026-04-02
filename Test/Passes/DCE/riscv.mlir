// RUN: veir-opt %s -p=dce| filecheck %s

"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6():
        %18 = "riscv.li"() <{"value" = 1 : i64}> : () -> !reg
        %19 = "builtin.unrealized_conversion_cast"(%18) : (!reg) -> i64
        %16 = "riscv.li"() <{"value" = 2 : i64}> : () -> !reg
        %17 = "builtin.unrealized_conversion_cast"(%16) : (!reg) -> i64
        %12 = "builtin.unrealized_conversion_cast"(%18) : (!reg) -> !reg
        %13 = "builtin.unrealized_conversion_cast"(%16) : (!reg) -> !reg
        %14 = "riscv.add"(%12, %13) : (!reg, !reg) -> !reg
        %15 = "builtin.unrealized_conversion_cast"(%14) : (!reg) -> i64
        "llvm.return"(%15) : (i64) -> ()
        // CHECK:      %{{.*}} = "riscv.li"() <{"value" = 1 : i64}> : () -> !reg
        // CHECK-NEXT: %{{.*}} = "riscv.li"() <{"value" = 2 : i64}> : () -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> !reg  
        // CHECK-NEXT: %{{.*}} = "riscv.add"(%{{.*}}, %{{.*}}) : (!reg, !reg) -> !reg
        // CHECK-NEXT: %{{.*}} = "builtin.unrealized_conversion_cast"(%{{.*}}) : (!reg) -> i64
        // CHECK-NEXT: "llvm.return"(%{{.*}}) : (i64) -> ()
    }) : () -> ()
}) : () -> ()
