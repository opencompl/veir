// RUN: ./Tools/vcc --emit-mlir -O %s -o - | filecheck %s
// RUN: ./Tools/vcc -c %s -o %t.o
// RUN: test -s %t.o
// RUN: ./Tools/vcc -S %s -o %t.s
// RUN: test -s %t.s

unsigned d1(unsigned p, unsigned q) {
  return ~(~p & ~q);
}

unsigned short d2(unsigned short p, unsigned short q) {
  return ~(~p | ~q);
}

// d1 should fold to a single `or` of the arguments.
// CHECK-LABEL: "sym_name" = "d1"
// CHECK-NOT:   "llvm.xor"
// CHECK-NOT:   "llvm.and"
// CHECK:       "llvm.or"
// CHECK-NOT:   "llvm.xor"
// CHECK:       "llvm.return"

// d2 should fold to an `and` (sandwiched between the zext/trunc).
// CHECK-LABEL: "sym_name" = "d2"
// CHECK-NOT:   "llvm.xor"
// CHECK-NOT:   "llvm.or"
// CHECK:       "llvm.and"
// CHECK-NOT:   "llvm.xor"
// CHECK:       "llvm.return"
