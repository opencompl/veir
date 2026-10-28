// RUN: veir-opt %s -p=legalize-riscv64 | filecheck %s
// RUN: veir-opt %s -p=legalize-riscv64,postlegalizer-combiner-riscv64 | filecheck %s --check-prefix=COMBINE

// `g_br` is always legal. The condition of `g_brcond` is widened to `i64` with a `g_zext`, which is
// lowered to a mask of the low bit. For a `g_icmp` condition, the mask is combined away (by the
// artifact combiner or by `redundant_and`), so the `g_brcond` branches on the `g_icmp` itself.

"builtin.module"() ({
  "llvm.func"() <{sym_name = "f", function_type = !llvm.func<i64 (i32, i32, i1)>}> ({
  ^bb0(%x: i32, %y: i32, %c: i1):
    %cmp = "gmir.g_icmp"(%x, %y) <{predicate = 2 : i64}> : (i32, i32) -> i1
    "gmir.g_brcond"(%cmp) [^bb1, ^bb2] <{operandSegmentSizes = array<i32: 1, 0, 0>}> : (i1) -> ()
  ^bb1:
    %x64 = "gmir.g_sext"(%x) : (i32) -> i64
    "gmir.g_brcond"(%c, %x64) [^bb2, ^bb3] <{operandSegmentSizes = array<i32: 1, 0, 1>}> : (i1, i64) -> ()
  ^bb2:
    %zero = "gmir.g_constant"() <{value = 0 : i64}> : () -> i64
    "gmir.g_br"(%zero) [^bb3] : (i64) -> ()
  ^bb3(%r: i64):
    "llvm.return"(%r) : (i64) -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "gmir.g_icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
// CHECK:      %[[EXT:.*]] = "gmir.g_anyext"(%{{.*}}) : (i1) -> i64
// CHECK-NEXT: %[[MASK:.*]] = "gmir.g_constant"() <{"value" = 1 : i64}> : () -> i64
// CHECK-NEXT: %[[AND:.*]] = "gmir.g_and"(%[[EXT]], %[[MASK]]) : (i64, i64) -> i64
// CHECK-NEXT: "gmir.g_brcond"(%[[AND]], %{{.*}}) [^{{.*}}, ^{{.*}}] <{"operandSegmentSizes" = array<i32: 1, 0, 1>}> : (i64, i64) -> ()
// CHECK:      "gmir.g_br"(%{{.*}}) [^{{.*}}] : (i64) -> ()

// COMBINE:      %[[CMP:.*]] = "gmir.g_icmp"(%{{.*}}, %{{.*}}) <{"predicate" = 2 : i64}> : (i64, i64) -> i64
// COMBINE-NEXT: "gmir.g_brcond"(%[[CMP]]) [^{{.*}}, ^{{.*}}] <{"operandSegmentSizes" = array<i32: 1, 0, 0>}> : (i64) -> ()
// COMBINE:      "gmir.g_and"
// COMBINE-NEXT: "gmir.g_brcond"
