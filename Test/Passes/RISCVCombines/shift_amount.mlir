// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s
// RUN: veir-opt %s -p=riscv-combine,dce,riscv-combine,dce | filecheck %s

// R1: only the low six (RV64) or five (word) bits of a register shift
// amount matter. Keep data operands and other uses of the producer intact.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "mask_shared"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %amount = "riscv.andi"(%a) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %r0 = "riscv.sll"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r1 = "riscv.srl"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r2 = "riscv.sra"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r3 = "riscv.sllw"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r4 = "riscv.srlw"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r5 = "riscv.sraw"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @mask_shared(%[[mask_shared_X:[^:]*]]: !riscv.reg, %[[mask_shared_A:[^:]*]]: !riscv.reg)
// CHECK-NOT: "riscv.andi"
// CHECK-NEXT: %[[mask_shared_R0:[^ ]*]] = "riscv.sll"(%[[mask_shared_X]], %[[mask_shared_A]])
// CHECK-NEXT: %[[mask_shared_R1:[^ ]*]] = "riscv.srl"(%[[mask_shared_X]], %[[mask_shared_A]])
// CHECK-NEXT: %[[mask_shared_R2:[^ ]*]] = "riscv.sra"(%[[mask_shared_X]], %[[mask_shared_A]])
// CHECK-NEXT: %[[mask_shared_R3:[^ ]*]] = "riscv.sllw"(%[[mask_shared_X]], %[[mask_shared_A]])
// CHECK-NEXT: %[[mask_shared_R4:[^ ]*]] = "riscv.srlw"(%[[mask_shared_X]], %[[mask_shared_A]])
// CHECK-NEXT: %[[mask_shared_R5:[^ ]*]] = "riscv.sraw"(%[[mask_shared_X]], %[[mask_shared_A]])
// CHECK-NEXT: "func.return"(%[[mask_shared_R0]], %[[mask_shared_R1]], %[[mask_shared_R2]], %[[mask_shared_R3]], %[[mask_shared_R4]], %[[mask_shared_R5]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "zext_shared"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %amount = "riscv.zextw"(%a) : (!riscv.reg) -> !riscv.reg
    %r0 = "riscv.sll"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r1 = "riscv.srl"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r2 = "riscv.sra"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r3 = "riscv.sllw"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r4 = "riscv.srlw"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r5 = "riscv.sraw"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @zext_shared(%[[zext_shared_X:[^:]*]]: !riscv.reg, %[[zext_shared_A:[^:]*]]: !riscv.reg)
// CHECK-NOT: "riscv.zextw"
// CHECK-NEXT: %[[zext_shared_R0:[^ ]*]] = "riscv.sll"(%[[zext_shared_X]], %[[zext_shared_A]])
// CHECK-NEXT: %[[zext_shared_R1:[^ ]*]] = "riscv.srl"(%[[zext_shared_X]], %[[zext_shared_A]])
// CHECK-NEXT: %[[zext_shared_R2:[^ ]*]] = "riscv.sra"(%[[zext_shared_X]], %[[zext_shared_A]])
// CHECK-NEXT: %[[zext_shared_R3:[^ ]*]] = "riscv.sllw"(%[[zext_shared_X]], %[[zext_shared_A]])
// CHECK-NEXT: %[[zext_shared_R4:[^ ]*]] = "riscv.srlw"(%[[zext_shared_X]], %[[zext_shared_A]])
// CHECK-NEXT: %[[zext_shared_R5:[^ ]*]] = "riscv.sraw"(%[[zext_shared_X]], %[[zext_shared_A]])
// CHECK-NEXT: "func.return"(%[[zext_shared_R0]], %[[zext_shared_R1]], %[[zext_shared_R2]], %[[zext_shared_R3]], %[[zext_shared_R4]], %[[zext_shared_R5]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "masks64"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %m0 = "riscv.andi"(%a) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
    %r0 = "riscv.sll"(%x, %m0) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %m1 = "riscv.andi"(%a) <{"value" = 127 : i64}> : (!riscv.reg) -> !riscv.reg
    %r1 = "riscv.srl"(%x, %m1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %m2 = "riscv.andi"(%a) <{"value" = -65 : i64}> : (!riscv.reg) -> !riscv.reg
    %r2 = "riscv.sra"(%x, %m2) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r0, %r1, %r2) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @masks64(%[[masks64_X:[^:]*]]: !riscv.reg, %[[masks64_A:[^:]*]]: !riscv.reg)
// CHECK-NOT: "riscv.andi"
// CHECK-NEXT: %[[masks64_R0:[^ ]*]] = "riscv.sll"(%[[masks64_X]], %[[masks64_A]])
// CHECK-NEXT: %[[masks64_R1:[^ ]*]] = "riscv.srl"(%[[masks64_X]], %[[masks64_A]])
// CHECK-NEXT: %[[masks64_R2:[^ ]*]] = "riscv.sra"(%[[masks64_X]], %[[masks64_A]])
// CHECK-NEXT: "func.return"(%[[masks64_R0]], %[[masks64_R1]], %[[masks64_R2]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg), sym_name = "masks32"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %m0 = "riscv.andi"(%a) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
    %r0 = "riscv.sllw"(%x, %m0) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %m1 = "riscv.andi"(%a) <{"value" = 95 : i64}> : (!riscv.reg) -> !riscv.reg
    %r1 = "riscv.srlw"(%x, %m1) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %m2 = "riscv.andi"(%a) <{"value" = -33 : i64}> : (!riscv.reg) -> !riscv.reg
    %r2 = "riscv.sraw"(%x, %m2) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r0, %r1, %r2) : (!riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @masks32(%[[masks32_X:[^:]*]]: !riscv.reg, %[[masks32_A:[^:]*]]: !riscv.reg)
// CHECK-NOT: "riscv.andi"
// CHECK-NEXT: %[[masks32_R0:[^ ]*]] = "riscv.sllw"(%[[masks32_X]], %[[masks32_A]])
// CHECK-NEXT: %[[masks32_R1:[^ ]*]] = "riscv.srlw"(%[[masks32_X]], %[[masks32_A]])
// CHECK-NEXT: %[[masks32_R2:[^ ]*]] = "riscv.sraw"(%[[masks32_X]], %[[masks32_A]])
// CHECK-NEXT: "func.return"(%[[masks32_R0]], %[[masks32_R1]], %[[masks32_R2]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "nested64"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %a0 = "riscv.zextw"(%a) : (!riscv.reg) -> !riscv.reg
    %a1 = "riscv.andi"(%a0) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %a2 = "riscv.andi"(%a1) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.srl"(%x, %a2) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @nested64(%[[nested64_X:[^:]*]]: !riscv.reg, %[[nested64_A:[^:]*]]: !riscv.reg)
// CHECK-NOT: "riscv.andi"
// CHECK-NOT: "riscv.zextw"
// CHECK-NEXT: %[[nested64_R:[^ ]*]] = "riscv.srl"(%[[nested64_X]], %[[nested64_A]])
// CHECK-NEXT: "func.return"(%[[nested64_R]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "nested32"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %a0 = "riscv.andi"(%a) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
    %a1 = "riscv.andi"(%a0) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
    %a2 = "riscv.zextw"(%a1) : (!riscv.reg) -> !riscv.reg
    %r = "riscv.sraw"(%x, %a2) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @nested32(%[[nested32_X:[^:]*]]: !riscv.reg, %[[nested32_A:[^:]*]]: !riscv.reg)
// CHECK-NOT: "riscv.andi"
// CHECK-NOT: "riscv.zextw"
// CHECK-NEXT: %[[nested32_R:[^ ]*]] = "riscv.sraw"(%[[nested32_X]], %[[nested32_A]])
// CHECK-NEXT: "func.return"(%[[nested32_R]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "other_mask_use"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %amount = "riscv.andi"(%a) <{"value" = 255 : i64}> : (!riscv.reg) -> !riscv.reg
    %r = "riscv.sll"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r, %amount) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @other_mask_use(%[[other_mask_use_X:[^:]*]]: !riscv.reg, %[[other_mask_use_A:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[other_mask_use_M:[^ ]*]] = "riscv.andi"(%[[other_mask_use_A]])
// CHECK-NEXT: %[[other_mask_use_R:[^ ]*]] = "riscv.sll"(%[[other_mask_use_X]], %[[other_mask_use_A]])
// CHECK-NEXT: "func.return"(%[[other_mask_use_R]], %[[other_mask_use_M]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "other_zext_use"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %amount = "riscv.zextw"(%a) : (!riscv.reg) -> !riscv.reg
    %r = "riscv.sll"(%x, %amount) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r, %amount) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @other_zext_use(%[[other_zext_use_X:[^:]*]]: !riscv.reg, %[[other_zext_use_A:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[other_zext_use_M:[^ ]*]] = "riscv.zextw"(%[[other_zext_use_A]])
// CHECK-NEXT: %[[other_zext_use_R:[^ ]*]] = "riscv.sll"(%[[other_zext_use_X]], %[[other_zext_use_A]])
// CHECK-NEXT: "func.return"(%[[other_zext_use_R]], %[[other_zext_use_M]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg), sym_name = "width_boundary"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %m = "riscv.andi"(%a) <{"value" = 31 : i64}> : (!riscv.reg) -> !riscv.reg
    %full = "riscv.sll"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %word = "riscv.sllw"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%full, %word) : (!riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @width_boundary(%[[width_boundary_X:[^:]*]]: !riscv.reg, %[[width_boundary_A:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[WIDTH_M:[^ ]*]] = "riscv.andi"(%[[width_boundary_A]]) <{"value" = 31 : i64}>
// CHECK-NEXT: %[[WIDTH_FULL:[^ ]*]] = "riscv.sll"(%[[width_boundary_X]], %[[WIDTH_M]])
// CHECK-NEXT: %[[WIDTH_WORD:[^ ]*]] = "riscv.sllw"(%[[width_boundary_X]], %[[width_boundary_A]])
// CHECK-NEXT: "func.return"(%[[WIDTH_FULL]], %[[WIDTH_WORD]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "needed_amount_bits"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %m = "riscv.andi"(%a) <{"value" = -2 : i64}> : (!riscv.reg) -> !riscv.reg
    %r0 = "riscv.sll"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r1 = "riscv.srl"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r2 = "riscv.sra"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r3 = "riscv.sllw"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r4 = "riscv.srlw"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r5 = "riscv.sraw"(%x, %m) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%r0, %r1, %r2, %r3, %r4, %r5) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @needed_amount_bits(%[[needed_amount_bits_X:[^:]*]]: !riscv.reg, %[[needed_amount_bits_A:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[KEPT_M:[^ ]*]] = "riscv.andi"(%[[needed_amount_bits_A]]) <{"value" = -2 : i64}>
// CHECK-NEXT: %[[KEPT_R0:[^ ]*]] = "riscv.sll"(%[[needed_amount_bits_X]], %[[KEPT_M]])
// CHECK-NEXT: %[[KEPT_R1:[^ ]*]] = "riscv.srl"(%[[needed_amount_bits_X]], %[[KEPT_M]])
// CHECK-NEXT: %[[KEPT_R2:[^ ]*]] = "riscv.sra"(%[[needed_amount_bits_X]], %[[KEPT_M]])
// CHECK-NEXT: %[[KEPT_R3:[^ ]*]] = "riscv.sllw"(%[[needed_amount_bits_X]], %[[KEPT_M]])
// CHECK-NEXT: %[[KEPT_R4:[^ ]*]] = "riscv.srlw"(%[[needed_amount_bits_X]], %[[KEPT_M]])
// CHECK-NEXT: %[[KEPT_R5:[^ ]*]] = "riscv.sraw"(%[[needed_amount_bits_X]], %[[KEPT_M]])
// CHECK-NEXT: "func.return"(%[[KEPT_R0]], %[[KEPT_R1]], %[[KEPT_R2]], %[[KEPT_R3]], %[[KEPT_R4]], %[[KEPT_R5]])

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg), sym_name = "data_operands"}> ({
  ^bb0(%x: !riscv.reg, %a: !riscv.reg):
    %m = "riscv.andi"(%x) <{"value" = 63 : i64}> : (!riscv.reg) -> !riscv.reg
    %z = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %m0 = "riscv.sll"(%m, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %z0 = "riscv.sll"(%z, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %m1 = "riscv.srl"(%m, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %z1 = "riscv.srl"(%z, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %m2 = "riscv.sra"(%m, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %z2 = "riscv.sra"(%z, %a) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%m0, %z0, %m1, %z1, %m2, %z2) : (!riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg, !riscv.reg) -> ()
  }) : () -> ()

// CHECK: func.func @data_operands(%[[data_operands_X:[^:]*]]: !riscv.reg, %[[data_operands_A:[^:]*]]: !riscv.reg)
// CHECK-NEXT: %[[DATA_M:[^ ]*]] = "riscv.andi"(%[[data_operands_X]])
// CHECK-NEXT: %[[DATA_Z:[^ ]*]] = "riscv.zextw"(%[[data_operands_X]])
// CHECK-NEXT: %[[DATA_m0:[^ ]*]] = "riscv.sll"(%[[DATA_M]], %[[data_operands_A]])
// CHECK-NEXT: %[[DATA_z0:[^ ]*]] = "riscv.sll"(%[[DATA_Z]], %[[data_operands_A]])
// CHECK-NEXT: %[[DATA_m1:[^ ]*]] = "riscv.srl"(%[[DATA_M]], %[[data_operands_A]])
// CHECK-NEXT: %[[DATA_z1:[^ ]*]] = "riscv.srl"(%[[DATA_Z]], %[[data_operands_A]])
// CHECK-NEXT: %[[DATA_m2:[^ ]*]] = "riscv.sra"(%[[DATA_M]], %[[data_operands_A]])
// CHECK-NEXT: %[[DATA_z2:[^ ]*]] = "riscv.sra"(%[[DATA_Z]], %[[data_operands_A]])
// CHECK-NEXT: "func.return"(%[[DATA_m0]], %[[DATA_z0]], %[[DATA_m1]], %[[DATA_z1]], %[[DATA_m2]], %[[DATA_z2]])

}) : () -> ()
