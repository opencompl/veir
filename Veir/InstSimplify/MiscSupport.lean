import Veir.InstSimplify.IntrinsicSupport
import Veir.InstSimplify.ArithmeticExtra
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000

theorem gep_no_indices_iff (props : propertiesOf (.llvm .getelementptr : OpCode))
    (h : props.rawConstantIndices.values = #[])
    (p : LLVM.Ptr) (v : RuntimeValue) :
    InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)] #[.addr p] #[v] ↔
      v = .addr p := by
  have eval : ∀ memory, interpretOp' (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)] #[.addr p] #[] memory = .ok (#[.addr p], memory, none) := by
    intro memory
    cases p with
    | poison => simp [interpretOp', Llvm.interpretOp', h, GEPIndex.decode, DataLayout.gepOffsets]
    | val p =>
      have he : UInt64.ofInt (p.address.toNat : Int) = p.address := by
        have hlt : (p.address.toNat : Int) < 18446744073709551616 := by
          have := UInt64.toNat_lt p.address
          omega
        simp [UInt64.ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]
      cases p
      simp_all [interpretOp', Llvm.interpretOp', GEPIndex.decode, DataLayout.gepOffsets]
  constructor
  · intro hi
    have hh := hi.2 .empty
    rw [eval] at hh
    simpa using hh.symm
  · rintro rfl
    refine ⟨?_, eval⟩
    simp [RuntimeValue.ArrayConforms]
theorem misc_trunc_iff (src dst : IntegerType)
    (p : propertiesOf (.llvm .trunc : OpCode)) (x : LLVM.Int src.bitwidth) (v : RuntimeValue)
    (hw : dst.bitwidth < src.bitwidth) :
    InterpretsTo (.llvm .trunc) p #[dst] #[.int src.bitwidth x] #[v] ↔
      v = .int dst.bitwidth (LLVM.Int.trunc x dst.bitwidth p.nsw p.nuw hw) := by
  cases src; cases dst
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', TypeAttr.of_val, Attribute.of,
    -Attribute.integerType_eq_of, RuntimeValue.ArrayConforms, RuntimeValue.Conforms, Nat.not_le_of_gt hw]
  constructor
  · rintro ⟨_, h⟩; exact (h .empty).symm
  · grind

theorem misc_zext_iff (src dst : IntegerType)
    (p : propertiesOf (.llvm .zext : OpCode)) (x : LLVM.Int src.bitwidth) (v : RuntimeValue)
    (hw : src.bitwidth < dst.bitwidth) :
    InterpretsTo (.llvm .zext) p #[dst] #[.int src.bitwidth x] #[v] ↔
      v = .int dst.bitwidth (LLVM.Int.zext x dst.bitwidth p.nneg hw) := by
  cases src; cases dst
  simp [InterpretsTo, interpretOp', Llvm.interpretOp', TypeAttr.of_val, Attribute.of,
    -Attribute.integerType_eq_of, RuntimeValue.ArrayConforms, RuntimeValue.Conforms, Nat.not_le_of_gt hw]
  constructor
  · rintro ⟨_, h⟩; exact (h .empty).symm
  · grind

theorem misc_bitcast_int_eq (ty : IntegerType) (p : propertiesOf (.llvm .bitcast : OpCode))
    (x : LLVM.Int ty.bitwidth) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .bitcast) p #[ty] #[.int ty.bitwidth x] #[v]) : v = .int ty.bitwidth x := by
  cases ty
  have he := hi.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp at he
  exact he.symm

theorem misc_bitcast_ptr_eq (p : propertiesOf (.llvm .bitcast : OpCode))
    (x : LLVM.Ptr) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .bitcast) p #[(LLVM.PointerType.mk : TypeAttr)] #[.addr x] #[v]) : v = .addr x := by
  have he := hi.2 MemoryState.empty
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp at he
  exact he.symm

end Veir.InstSimplify
