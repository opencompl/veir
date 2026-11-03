// RUN: veir-opt %s -p=riscv > %t
// RUN: veir2mir %t | filecheck %s

// A function with ten arguments. The standard calling convention passes the
// first eight in a0-a7 (x10-x17) and the last two in the caller's outgoing
// argument area, at offsets 0 and 8 from the incoming `sp`. These must be
// loaded from fixed stack objects, not read from x18-x19, which are
// callee-saved registers holding whatever the caller left there.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i64 (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)>}> ({
  ^bb0(%a0: i64, %a1: i64, %a2: i64, %a3: i64, %a4: i64, %a5: i64, %a6: i64, %a7: i64, %a8: i64, %a9: i64):
    %s = "llvm.add"(%a8, %a9) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    %t = "llvm.add"(%s, %a0) <{overflowFlags = 0 : i32}> : (i64, i64) -> i64
    "llvm.return"(%t) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// Only the eight argument registers are liveins.
// CHECK:      name:            f
// CHECK:      liveins:
// CHECK-NEXT:   - { reg: '$x10' }
// CHECK:        - { reg: '$x17' }
// CHECK-NEXT: fixedStack:
// CHECK-NEXT:   - { id: 0, offset: 0, size: 8, alignment: 16, isImmutable: true }
// CHECK-NEXT:   - { id: 1, offset: 8, size: 8, alignment: 8, isImmutable: true }

// CHECK:      bb.0:
// CHECK-NEXT:   liveins: $x10, $x11, $x12, $x13, $x14, $x15, $x16, $x17
// CHECK:        COPY $x17
// CHECK-NEXT:   [[A8:%[a-z0-9_]+]]:gpr = LD %fixed-stack.0, 0 :: (load (s64) from %fixed-stack.0, align 16)
// CHECK-NEXT:   [[A9:%[a-z0-9_]+]]:gpr = LD %fixed-stack.1, 0 :: (load (s64) from %fixed-stack.1)
// CHECK-NOT:    $x18
// CHECK-NOT:    UNHANDLED
