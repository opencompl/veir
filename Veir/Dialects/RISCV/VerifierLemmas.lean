module

public import Veir.Dialects.RISCV.OpInfo
import all Veir.Dialects.RISCV.OpInfo

public section

/-!
# Facts from the RISC-V verifier

What a successful run of the verifier helpers the RISC-V dialects share tells about an operation.
-/

namespace Veir

/-- Every result of an operation that `verifyRISCVRegisterTypes` accepts has a register type. -/
theorem OperationPtr.verifyRISCVRegisterTypes_eq_ok {OpInfo : Type} [HasOpInfo OpInfo]
    {op : OperationPtr} {ctx : WfIRContext OpInfo} {opIn : op.InBounds ctx.raw}
    (h : op.verifyRISCVRegisterTypes ctx opIn = .ok ()) :
    ∀ i < op.getNumResults! ctx.raw,
      ∃ rt, (op.getResult i).getType! ctx.raw = .of RegisterType rt := by
  simp only [verifyRISCVRegisterTypes] at h
  rw [getNumResults!_eq_getNumResults opIn]
  refine Std.Legacy.Range.forIn_except_ok _ (fun a s hs => ?_)
    (Except.ok_left_of_bind_ok (Except.ok_of_bind_ok h))
  split at hs
  · next _ hT =>
    simp only [pure, Except.pure, Except.ok.injEq] at hs
    exact ⟨hs.symm, _, TypeAttr.inj.mpr
      (by simpa only [TypeAttr.of_val, Attribute.of_def, IsAttr.inject] using hT)⟩
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs

end Veir

end
