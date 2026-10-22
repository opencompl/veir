import Veir.InstSimplify.GEPZeroSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option backward.isDefEq.respectTransparency false

theorem gep_all_zero_refines (props : propertiesOf (.llvm .getelementptr : OpCode))
    (indices : Array RuntimeValue)
    (hz : ∀ i ∈ props.rawConstantIndices.values, i = 0 ∨ i = -2147483648)
    (hd : ∀ index ∈ indices, GEPValueZero index)
    (hcount : (props.rawConstantIndices.values.filter (· == -2147483648)).size = indices.size)
    (p : LLVM.Ptr) (v : RuntimeValue)
    (hi : InterpretsTo (.llvm .getelementptr) props #[(LLVM.PointerType.mk : TypeAttr)]
      (#[.addr p] ++ indices) #[v]) : v ⊒ .addr p := by
  have hdecode := gep_decode_zero_indices props.rawConstantIndices.values indices hz hd hcount
  have he := hi.2 .empty
  rcases gep_zeroish_offsets DataLayout.riscv64 props.elem_type.val _ hdecode with hn | ⟨dynamic,hn,hzero⟩
  · simp [interpretOp', Llvm.interpretOp', hn] at he
  · cases p with
    | poison =>
      simp [interpretOp', Llvm.interpretOp', hn] at he
      subst v
      simp [RuntimeValue.isRefinedBy, isRefinedBy]
    | val p =>
      have hu : UInt64.ofInt (p.address.toNat : Int) = p.address := by
        have hlt : (p.address.toNat : Int) < 18446744073709551616 := by
          have := UInt64.toNat_lt p.address
          omega
        simp [UInt64.ofInt, Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt]
      have hloop := gep_address_zero_loop MemoryState.empty dynamic hzero (p.address.toNat : Int)
      simp [interpretOp', Llvm.interpretOp', hn] at he
      conv at he =>
        lhs
        arg 1
        arg 3
        tactic =>
          refine show _ = gepAddressStep MemoryState.empty from ?_
          funext x state
          rcases x with ⟨value,stride⟩
          cases value <;> try rfl
      rw [hloop] at he
      simp [hu] at he
      subst v
      simp [RuntimeValue.isRefinedBy, isRefinedBy]

end Veir.InstSimplify
