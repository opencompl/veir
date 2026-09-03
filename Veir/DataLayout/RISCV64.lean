module

public import Veir.Interfaces.DataLayoutInterfaces

/-!
# RV64 Data Layout

The fixed data layout used by the RV64 backend.
-/

namespace Veir.DataLayout

/-- The smallest power of two greater than or equal to `n` (and `1` for `0`). -/
private def powerOfTwoCeil (n : Nat) : Nat :=
  if n ≤ 1 then 1 else 2 ^ (Nat.log2 (n - 1) + 1)

/--
  RV64 integer ABI alignment, derived from LLVM's
  `i1:8-i8:8-i16:16-i32:32-i64:64-i128:128` layout entries. As in LLVM and
  MLIR, an unlisted width uses the next larger entry, or the largest entry when
  no larger one exists.
-/
private def rv64IntegerAlignment (bitwidth : Nat) : Nat :=
  if bitwidth ≤ 8 then 1
  else if bitwidth ≤ 16 then 2
  else if bitwidth ≤ 32 then 4
  else if bitwidth ≤ 64 then 8
  else 16

private def scalarInfo (size alignment : Nat) : DataLayoutTypeInfo :=
  { size
    abiAlignment := alignment
    preferredAlignment := alignment }

/-- Layout facts for the LLVM-compatible fixed-size types supported by VeIR. -/
private def queryRISCV64 (type : Attribute) : Option DataLayoutTypeInfo :=
  match type with
  | .integerType { bitwidth } | .byteType { bitwidth } =>
      if bitwidth = 0 then none
      else
        let size := (bitwidth + 7) / 8
        some (scalarInfo size (rv64IntegerAlignment bitwidth))
  | .floatType type =>
      let bitwidth := type.bitwidth
      if bitwidth = 0 then none
      else
        let size := (bitwidth + 7) / 8
        some (scalarInfo size (powerOfTwoCeil size))
  | .llvmPointerType _ =>
      some (scalarInfo 8 8)
  | .llvmArrayType { size, type } => do
      let element ← queryRISCV64 type
      some
        { size := element.allocSize * size
          abiAlignment := element.abiAlignment
          preferredAlignment := element.preferredAlignment }
  | _ => none

/--
  The standard RV64 data layout:
  `e-m:e-p:64:64-i64:64-i128:128-n32:64-S128`, together with LLVM's
  default primitive entries.
-/
public def riscv64 : DataLayout :=
  { query := queryRISCV64 }

end Veir.DataLayout
