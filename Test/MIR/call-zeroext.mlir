// RUN: veir-opt %s --print-op-generic -p=riscv | veir2mir | filecheck %s

// The i8/i16 parameters arrive sign-extended, and the i1 parameter's upper
// bits are unspecified. Forwarding them to zeroext arguments must clear those
// bits. These entry-block casts survive reconciliation, so the MIR printer
// must implement their zero-extension rather than emitting COPYs.
"builtin.module"() ({
  "llvm.func"() <{sym_name = "main", function_type = !llvm.func<i64 (i8, i16, i1)>, arg_attrs = [{llvm.signext}, {llvm.signext}, {}]}> ({
    ^bb0(%b : i8, %h : i16, %c : i1):
      %r = "llvm.call"(%b, %h, %c) <{callee = @g, arg_attrs = [{llvm.zeroext}, {llvm.zeroext}, {llvm.zeroext}], operandSegmentSizes = array<i32: 3, 0>, op_bundle_sizes = array<i32>}> : (i8, i16, i1) -> i64
      "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
  "llvm.func"() <{sym_name = "g", function_type = !llvm.func<i64 (i8, i16, i1)>, arg_attrs = [{llvm.zeroext}, {llvm.zeroext}, {llvm.zeroext}]}> ({}) : () -> ()
}) : () -> ()

// CHECK:      bb.0:
// CHECK:      [[B:%arg[0-9]+_0]]:gpr = COPY $x10
// CHECK-NEXT: [[H:%arg[0-9]+_1]]:gpr = COPY $x11
// CHECK-NEXT: [[C:%arg[0-9]+_2]]:gpr = COPY $x12
// CHECK-NEXT: [[BZ:%v[0-9]+]]:gpr = ANDI [[B]], 255
// CHECK-NEXT: [[HZ:%v[0-9]+]]:gpr = ZEXT_H_RV64 [[H]]
// CHECK-NEXT: [[CZ:%v[0-9]+]]:gpr = ANDI [[C]], 1
// CHECK-NEXT: ADJCALLSTACKDOWN 0, 0, implicit-def dead $x2, implicit $x2
// CHECK-NEXT: $x10 = COPY [[BZ]]
// CHECK-NEXT: $x11 = COPY [[HZ]]
// CHECK-NEXT: $x12 = COPY [[CZ]]
// CHECK-NEXT: PseudoCALL target-flags(riscv-call) @g
