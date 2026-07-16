// RUN: veir-opt %s -p=riscv-combine | filecheck %s

// Byte- and half-word mirrors of `zextw_li_low32`/`sextw_li_low32`: a `riscv.li`
// constant already carrying the extension's high-bit pattern makes the extension
// redundant. Zero-extension is a no-op on the unsigned range `[0, 2^width)`;
// sign-extension on the signed range `[-2^(width-1), 2^(width-1))`.

"builtin.module"() ({
  // zextb: 200 is in [0, 2^8) -> fold.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f0"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = 200 : i32}> : () -> !riscv.reg
    %z = "riscv.zextb"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  // zexth: 1000 is in [0, 2^16) -> fold.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f1"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = 1000 : i32}> : () -> !riscv.reg
    %z = "riscv.zexth"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  // sextb: -100 is in [-2^7, 2^7) -> fold.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f2"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = -100 : i32}> : () -> !riscv.reg
    %z = "riscv.sextb"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  // sexth: -1000 is in [-2^15, 2^15) -> fold.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f3"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = -1000 : i32}> : () -> !riscv.reg
    %z = "riscv.sexth"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: 200 is outside the *signed* byte range [-128, 128), so its
  // sign-extension differs -- the `sextb` must stay.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f4"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = 200 : i32}> : () -> !riscv.reg
    %z = "riscv.sextb"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()

  // Negative case: a negative immediate is sign-extended, so bits above the byte
  // aren't clear -- the `zextb` must stay.
  "func.func"() <{function_type = () -> !riscv.reg, sym_name = "f5"}> ({
  ^bb0():
    %c = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
    %z = "riscv.zextb"(%c) : (!riscv.reg) -> !riscv.reg
    "func.return"(%z) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      %[[ZB:.*]] = "riscv.li"() <{"value" = 200 : i32}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ZB]]) : (!riscv.reg) -> ()

// CHECK:      %[[ZH:.*]] = "riscv.li"() <{"value" = 1000 : i32}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[ZH]]) : (!riscv.reg) -> ()

// CHECK:      %[[SB:.*]] = "riscv.li"() <{"value" = -100 : i32}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SB]]) : (!riscv.reg) -> ()

// CHECK:      %[[SH:.*]] = "riscv.li"() <{"value" = -1000 : i32}> : () -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[SH]]) : (!riscv.reg) -> ()

// CHECK:      %[[NSB_C:.*]] = "riscv.li"() <{"value" = 200 : i32}> : () -> !riscv.reg
// CHECK-NEXT: %[[NSB_Z:.*]] = "riscv.sextb"(%[[NSB_C]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[NSB_Z]]) : (!riscv.reg) -> ()

// CHECK:      %[[NZB_C:.*]] = "riscv.li"() <{"value" = -1 : i32}> : () -> !riscv.reg
// CHECK-NEXT: %[[NZB_Z:.*]] = "riscv.zextb"(%[[NZB_C]]) : (!riscv.reg) -> !riscv.reg
// CHECK-NEXT: "func.return"(%[[NZB_Z]]) : (!riscv.reg) -> ()
