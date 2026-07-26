module

public import Veir.Interpreter.Basic

/-!
  # Reading constant-like values

  This module provides a read-only bridge from constant-like IR operations to
  the runtime values used by the interpreter. Analyses can use it to seed
  constant facts without duplicating the interpretation of each constant
  spelling.
-/

public section

namespace Veir

/--
  If `val` is defined by a supported constant-like operation, return the
  runtime value it materializes.

  The conversions match the interpretation of the corresponding operations in
  `interpretOp'`. Since `mod_arith` has no interpreter semantics, its constants
  are recognized only when they satisfy the canonical-residue invariant
  expected by the `mod-arith-to-arith` lowering.
-/
def ValuePtr.constantValue (val : ValuePtr) (ctx : IRContext OpCode) : Option RuntimeValue := do
  let defOp ← val.getDefiningOp! ctx
  match defOp.getOpType! ctx with
  | .arith .constant =>
    let .integerType intTy := (val.getType! ctx).val | none
    let bw := intTy.bitwidth
    let properties := defOp.getProperties! ctx (.arith .constant)
    return .int bw (.val (BitVec.ofInt bw properties.value.value))
  | .llvm .mlir__constant =>
    let .integerType intTy := (val.getType! ctx).val | none
    let bw := intTy.bitwidth
    let properties := defOp.getProperties! ctx (.llvm .mlir__constant)
    let .integer intAttr := properties.value | none
    return .int bw (Data.LLVM.Int.constant bw intAttr.value)
  | .llvm .mlir__poison =>
    let .integerType intTy := (val.getType! ctx).val | none
    return .int intTy.bitwidth (Data.LLVM.Int.mlir_poison intTy.bitwidth)
  | .riscv .li =>
    let .registerType _ := (val.getType! ctx).val | none
    let properties := defOp.getProperties! ctx (.riscv .li)
    return .reg (Data.RISCV.li (BitVec.ofInt 64 properties.value.value))
  | .mod_arith .constant =>
    let .modArithType mt := (val.getType! ctx).val | none
    let q := mt.modulus.value
    if q ≤ 0 then none else
    let properties := defOp.getProperties! ctx (.mod_arith .constant)
    let c := properties.value.value
    if c < 0 ∨ q ≤ c then none else
    return .int mt.modulus.type.bitwidth (.val (BitVec.ofInt mt.modulus.type.bitwidth c))
  | _ => none

end Veir
