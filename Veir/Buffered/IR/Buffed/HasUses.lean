module

public import Veir.Buffered.IR.Buffed.InBounds
import all Veir.Buffered.IR.Buffed.Basic

public section
namespace Veir.Buffered.Sim

variable {OpInfo : Type} [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]

private def hasUsesFrom (ctx : IRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx)
    (wf : ctx.spec.WellFormed)
    (index : Nat) (hi : index < (op.getNumResults ctx ib).toNat) : Bool :=
  have hindex : index.toUInt64.toNat = index := by
    have := UInt64.toNat_lt (op.getNumResults ctx ib)
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
    omega
  have hop := wf.operations op.spec ib.ib
  let result := op.getResultPtr ctx index.toUInt64 (by grind)
  match (result.getFirstUse ctx (by grind)).toOption with
  | some _ => true
  | none =>
    match index with
    | 0 => false
    | i + 1 => hasUsesFrom ctx op ib wf i (by omega)

private theorem result_spec (ctx : IRContext OpInfo) (op : OperationPtr)
    (ib : op.InBounds ctx) (index : UInt64) :
    (op.getResultPtr ctx index ib).spec = op.spec.getResult index.toNat := by
  simp [OperationPtr.getResultPtr, OpResultPtr.spec, OperationPtr.spec, Erased.map_out]

private theorem firstUse_none_iff (ctx : IRContext OpInfo) (op : OperationPtr)
    (ib : op.InBounds ctx) (index : UInt64) (hr : (op.getResultPtr ctx index ib).InBounds ctx) :
    ((op.getResultPtr ctx index ib).getFirstUse ctx hr).toOption = none ↔
      ((op.spec.getResult index.toNat).get! ctx.spec).firstUse = none := by
  have hfields := ctx.fieldsInBounds
  rw [OptionOpOperandPtr.toOption_none_iff_spec_none (ctx := ctx) (by grind)]
  rw [OpResultPtr.getFirstUse_spec, ← Veir.Buffered.OpResultPtr.get!_eq_get]
  rw [result_spec]

private theorem hasUsesFrom_spec (ctx : IRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx)
    (wf : ctx.spec.WellFormed) (index : Nat) (hi : index < (op.getNumResults ctx ib).toNat) :
    hasUsesFrom ctx op ib wf index hi = Veir.Buffered.OperationPtr.hasUses!.loop op.spec ctx.spec index := by
  have hcap := (wf.operations op.spec ib.ib).capResults_eq_numResults
  induction index with
  | zero =>
    have := firstUse_none_iff ctx op ib 0 (by grind)
    rw [hasUsesFrom.eq_def]
    simp only [Veir.Buffered.OperationPtr.hasUses!.loop]
    split <;> grind
  | succ i ih =>
    have hindex : (i + 1).toUInt64.toNat = i + 1 := by
      have := UInt64.toNat_lt (op.getNumResults ctx ib)
      simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']
      omega
    have := firstUse_none_iff ctx op ib (i + 1).toUInt64 (by grind)
    rw [hasUsesFrom.eq_def]
    simp only [Veir.Buffered.OperationPtr.hasUses!.loop]
    have := ih (by omega)
    split <;> grind

/-- Inspect the reverse-use lists without evaluating the erased specification. -/
@[inline]
def OperationPtr.hasUses (ctx : IRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx)
    (wf : ctx.spec.WellFormed) : Bool :=
  let count := (op.getNumResults ctx ib).toNat
  if h : count = 0 then false else hasUsesFrom ctx op ib wf (count - 1) (by omega)

@[grind =]
theorem OperationPtr.hasUses_spec (ctx : IRContext OpInfo) (op : OperationPtr) (ib : op.InBounds ctx)
    (wf : ctx.spec.WellFormed) : op.hasUses ctx ib wf = op.spec.hasUses! ctx.spec := by
  simp only [hasUses, Veir.Buffered.OperationPtr.hasUses!]
  have hop := (wf.operations op.spec ib.ib).capResults_eq_numResults
  have hrepr := ctx.isRepr.operations_indices op.spec ib.ib
  have heq : (op.getNumResults ctx ib).toNat = op.spec.getNumResults! ctx.spec := by grind
  split
  · grind
  · rw [hasUsesFrom_spec]
    grind

end Veir.Buffered.Sim
