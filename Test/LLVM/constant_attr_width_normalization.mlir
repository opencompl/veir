// RUN: VEIR_ROUNDTRIP
// RUN: MLIR_ROUNDTRIP

// An MLIR `IntegerAttr` *is* an APInt of its declared width, so MLIR normalizes
// the literal at parse time and the round trip is observable:
//
//   mlir-opt:  llvm.mlir.constant(200 : i8)         -> llvm.mlir.constant(-56 : i8)
//              llvm.mlir.constant(3 : i2)           -> llvm.mlir.constant(-1 : i2)
//              llvm.mlir.constant(4294967295 : i32) -> llvm.mlir.constant(-1 : i32)
//              llvm.mlir.constant(-1 : i1)          -> llvm.mlir.constant(true)
//
// `LLVMConstantProperties.fromAttrDict` reduces the literal the same way.
//
// Note: Veir prints a width-1 attribute as `1 : i1` where MLIR prints `true`.
// Both denote the same attribute and each parser accepts the other's form, so
// only the *value* is pinned here, not the `true`/`false` spelling.
//
// The attribute type matches the result type throughout: `llvm.mlir.constant`
// requires that ("attribute and type have different integer types"), so a
// mismatched pair would not survive the `mlir-opt` leg of the round trip. The
// widening and narrowing that MLIR applies when the two differ is covered by
// Test/Interpreter/LLVM/constant_attr_*.mlir.

"builtin.module"() ({
  "llvm.func"() <{CConv = #llvm.cconv<ccc>, function_type = !llvm.func<void ()>, linkage = #llvm.linkage<external>, sym_name = "constants", visibility_ = 0 : i64}> ({
    %0 = "llvm.mlir.constant"() <{value = 200 : i8}> : () -> i8
    %1 = "llvm.mlir.constant"() <{value = 3 : i2}> : () -> i2
    %2 = "llvm.mlir.constant"() <{value = 4294967295 : i32}> : () -> i32
    %3 = "llvm.mlir.constant"() <{value = -1 : i1}> : () -> i1
    // Already normalized: must round-trip unchanged.
    %4 = "llvm.mlir.constant"() <{value = -3 : i8}> : () -> i8
    %5 = "llvm.mlir.constant"() <{value = true}> : () -> i1
    %6 = "llvm.mlir.constant"() <{value = 300 : i32}> : () -> i32
    "llvm.return"() : () -> ()
  }) : () -> ()
}) : () -> ()

// CHECK:      "llvm.mlir.constant"() <{"value" = -56 : i8}> : () -> i8
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = -1 : i2}> : () -> i2
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = -1 : i32}> : () -> i32
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = -3 : i8}> : () -> i8
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 1 : i1}> : () -> i1
// CHECK-NEXT: "llvm.mlir.constant"() <{"value" = 300 : i32}> : () -> i32

// This module's constants are dead, so lowering it all the way to LLVM IR
// yields nothing to look at (`define void @constants() { ret void }`).  The
// reference for this test is the llvm-dialect form, where the normalization is
// visible:
//
//   mlir-opt Test/LLVM/constant_attr_width_normalization.mlir
//
// (module body, the printer wraps it in `module { ... }`)
//
//   llvm.func @constants() {
//     %0 = llvm.mlir.constant(-56 : i8) : i8
//     %1 = llvm.mlir.constant(-1 : i2) : i2
//     %2 = llvm.mlir.constant(-1 : i32) : i32
//     %3 = llvm.mlir.constant(true) : i1
//     %4 = llvm.mlir.constant(-3 : i8) : i8
//     %5 = llvm.mlir.constant(true) : i1
//     %6 = llvm.mlir.constant(300 : i32) : i32
//     llvm.return
//   }
