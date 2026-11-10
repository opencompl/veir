// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s

"builtin.module"() ({
  // Revisit the shift until both nested masks and the zero extension are gone.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "nested_amount"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %z = "riscv.zextw"(%a) : (!riscv.reg) -> !riscv.reg
    %inner = "riscv.andi"(%z) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %outer = "riscv.andi"(%inner) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srl"(%x, %outer) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  // Five amount bits suffice for SLLW, but SLL must retain bit 5 as well.
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "width_boundary"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %m = "riscv.andi"(%a) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
    %full = "riscv.sll"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %word = "riscv.sllw"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%full, %word) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

  // Each producer feeds both operands: bypass the amount, preserving the data use.
  "func.func"() <{function_type = (!riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "shared_data"}> ({
  ^bb0(%a: !riscv.reg):
    %m = "riscv.andi"(%a) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %z = "riscv.zextw"(%a) : (!riscv.reg) -> !riscv.reg
    %masked = "riscv.sra"(%m, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %extended = "riscv.srl"(%z, %z) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%masked, %extended) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK: func.func @nested_amount(%[[X:[^:]*]]: !riscv.reg, %[[A:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[R:[^ ]*]] = "riscv.srl"(%[[X]], %[[A]])
// CHECK-NEXT: "func.return"(%[[R]])

// CHECK: func.func @width_boundary(%[[WX:[^:]*]]: !riscv.reg, %[[WA:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[M:[^ ]*]] = "riscv.andi"(%[[WA]]) <{"value" = 31 : i64}>
// CHECK-NEXT: %[[FULL:[^ ]*]] = "riscv.sll"(%[[WX]], %[[M]])
// CHECK-NEXT: %[[WORD:[^ ]*]] = "riscv.sllw"(%[[WX]], %[[WA]])
// CHECK-NEXT: "func.return"(%[[FULL]], %[[WORD]])

// CHECK: func.func @shared_data(%[[SA:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[SM:[^ ]*]] = "riscv.andi"(%[[SA]]) <{"value" = 63 : i64}>
// CHECK-NEXT: %[[SZ:[^ ]*]] = "riscv.zextw"(%[[SA]])
// CHECK-NEXT: %[[MASKED:[^ ]*]] = "riscv.sra"(%[[SM]], %[[SA]])
// CHECK-NEXT: %[[EXTENDED:[^ ]*]] = "riscv.srl"(%[[SZ]], %[[SA]])
// CHECK-NEXT: "func.return"(%[[MASKED]], %[[EXTENDED]])
