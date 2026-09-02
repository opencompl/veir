// RUN: veir-opt %s -p=riscv-combine | filecheck %s --check-prefix=COMBINE
// RUN: veir-opt %s -p=riscv-combine,dce | filecheck %s --check-prefix=CLEAN

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "positive"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %q = "riscv.xor"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r = "riscv.roriw"(%q) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "shared_xor"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %q = "riscv.xor"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r = "riscv.roriw"(%q) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
    "test.test"(%q) : (!riscv.reg) -> ()
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "one_zextw"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %q = "riscv.xor"(%zx, %y) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r = "riscv.roriw"(%q) <{"value" = 12 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()

  "func.func"() <{function_type = (!riscv.reg, !riscv.reg) -> !riscv.reg, sym_name = "rori_negative"}> ({
  ^bb0(%x: !riscv.reg, %y: !riscv.reg):
    %zx = "riscv.zextw"(%x) : (!riscv.reg) -> !riscv.reg
    %zy = "riscv.zextw"(%y) : (!riscv.reg) -> !riscv.reg
    %q = "riscv.xor"(%zx, %zy) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    %r = "riscv.rori"(%q) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg
    "func.return"(%r) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// COMBINE-LABEL: "sym_name" = "positive"
// COMBINE:      ^{{.*}}(%[[POS_X:.*]] : !riscv.reg, %[[POS_Y:.*]] : !riscv.reg):
// COMBINE:      %[[POS_RAW_XOR:.*]] = "riscv.xor"(%[[POS_X]], %[[POS_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// COMBINE-NEXT: %[[POS_RORIW:.*]] = "riscv.roriw"(%[[POS_RAW_XOR]]) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
// COMBINE-NEXT: "func.return"(%[[POS_RORIW]]) : (!riscv.reg) -> ()

// COMBINE-LABEL: "sym_name" = "shared_xor"
// COMBINE:      ^{{.*}}(%[[SHARED_X:.*]] : !riscv.reg, %[[SHARED_Y:.*]] : !riscv.reg):
// COMBINE:      %[[SHARED_ZX:.*]] = "riscv.zextw"(%[[SHARED_X]]) : (!riscv.reg) -> !riscv.reg
// COMBINE:      %[[SHARED_ZY:.*]] = "riscv.zextw"(%[[SHARED_Y]]) : (!riscv.reg) -> !riscv.reg
// COMBINE:      %[[SHARED_OLD_XOR:.*]] = "riscv.xor"(%[[SHARED_ZX]], %[[SHARED_ZY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// COMBINE:      %[[SHARED_RAW_XOR:.*]] = "riscv.xor"(%[[SHARED_X]], %[[SHARED_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// COMBINE-NEXT: %[[SHARED_RORIW:.*]] = "riscv.roriw"(%[[SHARED_RAW_XOR]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
// COMBINE-NEXT: "test.test"(%[[SHARED_OLD_XOR]]) : (!riscv.reg) -> ()
// COMBINE-NEXT: "func.return"(%[[SHARED_RORIW]]) : (!riscv.reg) -> ()

// COMBINE-LABEL: "sym_name" = "one_zextw"
// COMBINE:      ^{{.*}}(%[[ONE_X:.*]] : !riscv.reg, %[[ONE_Y:.*]] : !riscv.reg):
// COMBINE-NEXT: %[[ONE_ZX:.*]] = "riscv.zextw"(%[[ONE_X]]) : (!riscv.reg) -> !riscv.reg
// COMBINE-NEXT: %[[ONE_XOR:.*]] = "riscv.xor"(%[[ONE_ZX]], %[[ONE_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// COMBINE-NEXT: %[[ONE_RORIW:.*]] = "riscv.roriw"(%[[ONE_XOR]]) <{"value" = 12 : i64}> : (!riscv.reg) -> !riscv.reg

// COMBINE-LABEL: "sym_name" = "rori_negative"
// COMBINE:      ^{{.*}}(%[[RORI_X:.*]] : !riscv.reg, %[[RORI_Y:.*]] : !riscv.reg):
// COMBINE-NEXT: %[[RORI_ZX:.*]] = "riscv.zextw"(%[[RORI_X]]) : (!riscv.reg) -> !riscv.reg
// COMBINE-NEXT: %[[RORI_ZY:.*]] = "riscv.zextw"(%[[RORI_Y]]) : (!riscv.reg) -> !riscv.reg
// COMBINE-NEXT: %[[RORI_XOR:.*]] = "riscv.xor"(%[[RORI_ZX]], %[[RORI_ZY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// COMBINE-NEXT: %[[RORI:.*]] = "riscv.rori"(%[[RORI_XOR]]) <{"value" = 32 : i64}> : (!riscv.reg) -> !riscv.reg

// CLEAN-LABEL: "sym_name" = "positive"
// CLEAN:      ^{{.*}}(%[[CLEAN_POS_X:.*]] : !riscv.reg, %[[CLEAN_POS_Y:.*]] : !riscv.reg):
// CLEAN-NOT:  "riscv.zextw"
// CLEAN:      %[[CLEAN_POS_XOR:.*]] = "riscv.xor"(%[[CLEAN_POS_X]], %[[CLEAN_POS_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CLEAN-NEXT: %[[CLEAN_POS_RORIW:.*]] = "riscv.roriw"(%[[CLEAN_POS_XOR]]) <{"value" = 16 : i64}> : (!riscv.reg) -> !riscv.reg
// CLEAN-NEXT: "func.return"(%[[CLEAN_POS_RORIW]]) : (!riscv.reg) -> ()
// CLEAN-NOT:  "riscv.zextw"

// CLEAN-LABEL: "sym_name" = "shared_xor"
// CLEAN:      ^{{.*}}(%[[CLEAN_SHARED_X:.*]] : !riscv.reg, %[[CLEAN_SHARED_Y:.*]] : !riscv.reg):
// CLEAN-NEXT: %[[CLEAN_SHARED_ZX:.*]] = "riscv.zextw"(%[[CLEAN_SHARED_X]]) : (!riscv.reg) -> !riscv.reg
// CLEAN-NEXT: %[[CLEAN_SHARED_ZY:.*]] = "riscv.zextw"(%[[CLEAN_SHARED_Y]]) : (!riscv.reg) -> !riscv.reg
// CLEAN-NEXT: %[[CLEAN_SHARED_OLD_XOR:.*]] = "riscv.xor"(%[[CLEAN_SHARED_ZX]], %[[CLEAN_SHARED_ZY]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CLEAN-NEXT: %[[CLEAN_SHARED_RAW_XOR:.*]] = "riscv.xor"(%[[CLEAN_SHARED_X]], %[[CLEAN_SHARED_Y]]) : (!riscv.reg, !riscv.reg) -> !riscv.reg
// CLEAN-NEXT: %[[CLEAN_SHARED_RORIW:.*]] = "riscv.roriw"(%[[CLEAN_SHARED_RAW_XOR]]) <{"value" = 7 : i64}> : (!riscv.reg) -> !riscv.reg
// CLEAN-NEXT: "test.test"(%[[CLEAN_SHARED_OLD_XOR]]) : (!riscv.reg) -> ()
// CLEAN-NEXT: "func.return"(%[[CLEAN_SHARED_RORIW]]) : (!riscv.reg) -> ()
