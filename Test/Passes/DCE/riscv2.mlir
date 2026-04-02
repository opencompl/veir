"builtin.module"() ({
  ^4():
    "func.func"() ({
      ^6():
        %7 = "riscv.li"() <{"value" = 1 : i64}> : () -> !reg
        %9 = "riscv.li"() <{"value" = 2 : i64}> : () -> !reg
        %11 = "builtin.unrealized_conversion_cast"(%7) : (!reg) -> !reg
        %12 = "builtin.unrealized_conversion_cast"(%9) : (!reg) -> !reg
        %13 = "riscv.add"(%11, %12) : (!reg, !reg) -> !reg
        %14 = "builtin.unrealized_conversion_cast"(%13) : (!reg) -> i64
        "llvm.return"(%14) : (i64) -> ()
    }) : () -> ()
}) : () -> ()