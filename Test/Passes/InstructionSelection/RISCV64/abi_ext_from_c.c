// REQUIRES: clang, mlir-translate, mlir-opt
// RUN: clang --target=riscv64-unknown-linux-gnu -O1 -S -emit-llvm -o - %s | mlir-translate --import-llvm | mlir-opt --mlir-print-op-generic --mlir-print-local-scope | veir-opt -p=riscv | filecheck %s

// clang marks RV64 boundaries with `signext`/`zeroext`: `_Bool` and unsigned
// narrow types (including plain `char`, which is unsigned on RISC-V) are
// zero-extended, signed narrow types are sign-extended, and every 32-bit value is
// sign-extended (`signext i32`), whatever its signedness. The callee extends
// return values and the caller extends arguments, as the psABI requires.

_Bool ret_bool(long x) { return x & 1; }
// CHECK-LABEL: "sym_name" = "ret_bool"
// CHECK: %[[R:.*]] = "riscv.andi"(%{{.*}}) <{"value" = 1 : i64}>
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

char ret_char(long x) { return x; }
// CHECK-LABEL: "sym_name" = "ret_char"
// CHECK: %[[R:.*]] = "riscv.zextb"
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

signed char ret_schar(long x) { return x; }
// CHECK-LABEL: "sym_name" = "ret_schar"
// CHECK: %[[R:.*]] = "riscv.sextb"
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

unsigned char ret_uchar(long x) { return x; }
// CHECK-LABEL: "sym_name" = "ret_uchar"
// CHECK: %[[R:.*]] = "riscv.zextb"
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

short ret_short(long x) { return x; }
// CHECK-LABEL: "sym_name" = "ret_short"
// CHECK: %[[R:.*]] = "riscv.sexth"
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

unsigned short ret_ushort(long x) { return x; }
// CHECK-LABEL: "sym_name" = "ret_ushort"
// CHECK: %[[R:.*]] = "riscv.zexth"
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

int ret_int(long x) { return x; }
// CHECK-LABEL: "sym_name" = "ret_int"
// CHECK: %[[R:.*]] = "riscv.sextw"
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

unsigned ret_uint(long x) { return x; }
// CHECK-LABEL: "sym_name" = "ret_uint"
// CHECK: %[[R:.*]] = "riscv.sextw"
// CHECK-NEXT: "riscv_cf.return"(%[[R]])

void take(_Bool, char, signed char, short, unsigned short, unsigned);

void caller(long x) { take(x & 1, x, x, x, x, x); }
// CHECK-LABEL: "sym_name" = "caller"
// CHECK-DAG: %[[A0:.*]] = "riscv.andi"(%{{.*}}) <{"value" = 1 : i64}>
// CHECK-DAG: %[[A2:.*]] = "riscv.sextb"
// CHECK-DAG: %[[A3:.*]] = "riscv.sexth"
// CHECK-DAG: %[[A5:.*]] = "riscv.sextw"
// CHECK: "riscv_cf.call"(%[[A0]], %{{.*}}, %[[A2]], %[[A3]], %{{.*}}, %[[A5]]) <{"callee" = @take}>
