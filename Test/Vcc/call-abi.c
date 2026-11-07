// RUN: ./Tools/vcc -S %s -o %t.s
// RUN: filecheck %s --input-file %t.s
// RUN: ./Tools/vcc -c %s -o %t.veir.o
// RUN: ./Tools/vcc --llvm-backend -c %s -o %t.llvm.o
// RUN: python3 -c "import pathlib, struct, sys; flags = [struct.unpack_from('<I', pathlib.Path(p).read_bytes(), 48)[0] for p in sys.argv[1:]]; assert all(f & 6 == 4 for f in flags), flags" %t.veir.o %t.llvm.o

// Both backends must emit ELF objects with EF_RISCV_FLOAT_ABI_DOUBLE (0x4),
// using the floating-point ABI mask 0x6 in the ELF64 e_flags field at byte 48.
// Integer-only calls preserve fs0-fs11 under lp64d; a soft-float call mask
// incorrectly makes LLVM spill and reload all twelve in these functions.
extern long external(long);

long direct(long x) {
  return external(x) + 1;
}

long indirect(long (*callee)(long), long x) {
  return callee(x) + 1;
}

// CHECK-LABEL: direct:
// CHECK-NOT: fsd
// CHECK: call external
// CHECK-NOT: fld
// CHECK: ret

// CHECK-LABEL: indirect:
// CHECK-NOT: fsd
// CHECK: jalr
// CHECK-NOT: fld
// CHECK: ret
