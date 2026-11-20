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
  | .integerType { bitwidth, .. } | .byteType { bitwidth } =>
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
  | .llvmStructType { packed, body, .. } => do
      let fields ← body.attach.mapM fun ⟨field, _⟩ => queryRISCV64 field
      some (structLayout fields packed).2
  | .vectorType { shape, elementType } => do
      let elementBitwidth ← elementType.bitwidthOfType
      if elementBitwidth = 0 then none else
      /- Vector elements are packed by bit width, without scalar allocation
         padding. Round the total to bytes, then align the vector to the next
         power of two of its byte size, as LLVM does. -/
      let size := (shape.foldl (· * ·) elementBitwidth + 7) / 8
      some (scalarInfo size (powerOfTwoCeil size))
  | _ => none
termination_by type
decreasing_by
  all_goals simp_wf
  · grind [LLVM.ArrayType.sizeOf_elems_type]
  · rename_i name hmem
    have := LLVM.StructType.sizeOf_elems_body (t := { name, packed, body }) hmem
    grind

/--
  The standard RV64 data layout:
  `e-m:e-p:64:64-i64:64-i128:128-n32:64-S128`, together with LLVM's
  default primitive entries.
-/
public def riscv64 : DataLayout :=
  { query := queryRISCV64 }

/-- The layout of an integer type: `(w + 7) / 8` bytes, aligned as LLVM's
`i1:8-i8:8-i16:16-i32:32-i64:64-i128:128` entries (see `rv64IntegerAlignment`). -/
@[simp] public theorem riscv64_query_integerType (t : IntegerType) :
    riscv64.query (.integerType t) =
      if t.bitwidth = 0 then none
      else
        let alignment := if t.bitwidth ≤ 8 then 1 else if t.bitwidth ≤ 16 then 2
          else if t.bitwidth ≤ 32 then 4 else if t.bitwidth ≤ 64 then 8 else 16
        some { size := (t.bitwidth + 7) / 8, abiAlignment := alignment,
               preferredAlignment := alignment } := by
  rcases t with ⟨w, s⟩
  simp only [riscv64]
  rw [queryRISCV64]
  simp [scalarInfo, rv64IntegerAlignment]

/-- The layout of a pointer: 8 bytes, aligned to 8. -/
@[simp] public theorem riscv64_query_llvmPointerType (p : LLVM.PointerType) :
    riscv64.query (.llvmPointerType p) =
      some { size := 8, abiAlignment := 8, preferredAlignment := 8 } := by
  simp only [riscv64]
  rw [queryRISCV64]
  simp [scalarInfo]

end Veir.DataLayout
