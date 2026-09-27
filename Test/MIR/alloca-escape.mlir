// RUN: veir2mir %s | filecheck %s

// An alloca whose address is used somewhere other than a load/store base
// cannot fold into an access, so it materializes as `ADDI %stack.N, 0`. The
// second object, used only as a store base, still folds. Both get a `stack`
// entry either way.

"builtin.module"() ({
  "func.func"() <{function_type = (!riscv.reg) -> i64, sym_name = "main"}> ({
  ^bb0(%x: !riscv.reg):
    %escapes = "riscv_stack.alloca"() <{"size" = 16 : i64, "alignment" = 8 : i64}> : () -> !riscv.reg
    %folds = "riscv_stack.alloca"() <{"size" = 8 : i64, "alignment" = 16 : i64}> : () -> !riscv.reg
    "riscv.sd"(%x, %folds) <{"value" = 0 : i64}> : (!riscv.reg, !riscv.reg) -> ()
    %sum = "riscv.add"(%escapes, %x) : (!riscv.reg, !riscv.reg) -> !riscv.reg
    "func.return"(%sum) : (!riscv.reg) -> ()
  }) : () -> ()
}) : () -> ()

// One object per alloca, in definition order, carrying its own alignment.
// CHECK:      stack:
// CHECK-NEXT:   - { id: 0, size: 16, alignment: 8 }
// CHECK-NEXT:   - { id: 1, size: 8, alignment: 16 }

// CHECK:      bb.0:
// CHECK:        [[X:%[a-z0-9_]+]]:gpr = COPY $x10
// The escaping object's address reaches a register; the folded one does not.
// CHECK-NEXT:   [[P:%[a-z0-9_]+]]:gpr = ADDI %stack.0, 0
// CHECK-NEXT:   SD [[X]], %stack.1, 0
// CHECK-NEXT:   [[SUM:%[a-z0-9_]+]]:gpr = ADD [[P]], [[X]]
// CHECK-NEXT:   $x10 = COPY [[SUM]]
// CHECK-NEXT:   PseudoRET implicit $x10
// CHECK-NOT:    UNHANDLED
