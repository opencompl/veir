module

public import Veir.Dialects.GMIR.ResultsConform
public import Veir.Interpreter.ResultsConform

import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.GMIR.Interpreter
import all Veir.Dialects.GMIR.OpInfo

public section

/-!
# The results of a CTree run of a gMIR operation conform to their types

Every gMIR opcode but `g_anyext`, `g_load` and `g_freeze` runs its `Interp` semantics in a CTree,
so the conformance of the results its CTree produces follows from
`GMIR.interpretOp'_results_conform`.

Those three interpret a CTree of their own, which chooses the value of the result: the high bits
of a widened result for `g_anyext` and `g_load`, and the whole of a frozen poison for `g_freeze`.
Each keeps the width its `Interp` interpreter gives the result, so `arrayConforms_int_congr`
carries the conformance of that result over to every value they may choose.
-/

open CTree

namespace Veir

/-- A gMIR opcode but `g_anyext`, `g_load` and `g_freeze` runs its `Interp` semantics. -/
private theorem gmir_interpretOp'_ctree_eq_lift {opT : GMIR} (h₁ : opT ≠ .g_anyext)
    (h₂ : opT ≠ .g_load) (h₃ : opT ≠ .g_freeze)
    (properties : propertiesOf (OpCode.gmir opT)) (resultTypes : Array TypeAttr)
    (operands : Array RuntimeValue) (bs : Array BlockPtr) (mem : MemoryState)
    (regions : Array RegionPtr) :
    CTree.interpretOp' (.gmir opT) properties resultTypes operands bs mem regions =
      monadLift (Veir.interpretOp' (.gmir opT) properties resultTypes operands bs mem) := by
  cases opT <;> simp_all [CTree.interpretOp', Veir.interpretOp', GMIR.interpretOpCTree]

/-- Every result the CTree of a verified `g_freeze` can produce conforms to its result type. -/
private theorem freeze_results_conform {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {operands vals : Array RuntimeValue} {mem mem' : MemoryState}
    {act : Option ControlFlowAction} {bs : Array BlockPtr} {regions : Array RegionPtr}
    (hType : op.getOpType! ctx.raw = .gmir .g_freeze) (hV : op.Verified ctx opIn)
    (hConf : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : CTree.MayReturn
      (CTree.interpretOp' (.gmir .g_freeze)
        (op.getProperties! ctx.raw (OpCode.gmir GMIR.g_freeze)) (op.getResultTypes! ctx.raw)
        operands bs mem regions) (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  simp only [CTree.interpretOp', GMIR.interpretOpCTree] at h
  split at h
  · next w v hOps =>
    simp only [CTree.MayReturn.pure_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    refine arrayConforms_int_congr (x := (Data.LLVM.Int.val v).freeze) ?_
    exact GMIR.interpretOp'_results_conform .g_freeze (bs := bs) (mem := mem) (mem' := mem)
      (act := none) hType hV hConf
      (by simp only [GMIR.interpretOp', hOps, Interp.pure_eq])
  · next w hOps =>
    simp only [Bind.bind, CTree.MayReturn.bind_iff,
      CTree.MayReturn.choose_iff, CTree.MayReturn.pure_iff, Prod.mk.injEq, true_and] at h
    obtain ⟨bv, rfl, -, -⟩ := h
    refine arrayConforms_int_congr (x := (Data.LLVM.Int.poison : Data.LLVM.Int w).freeze) ?_
    exact GMIR.interpretOp'_results_conform .g_freeze (bs := bs) (mem := mem) (mem' := mem)
      (act := none) hType hV hConf
      (by simp only [GMIR.interpretOp', hOps, Interp.pure_eq])
  · simp only [CTree.MayReturn.fail_iff] at h

private theorem anyext_results_conform {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {operands vals : Array RuntimeValue} {mem mem' : MemoryState}
    {act : Option ControlFlowAction} {bs : Array BlockPtr} {regions : Array RegionPtr}
    (hType : op.getOpType! ctx.raw = .gmir .g_anyext) (hV : op.Verified ctx opIn)
    (hConf : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : CTree.MayReturn
      (CTree.interpretOp' (.gmir .g_anyext)
        (op.getProperties! ctx.raw (OpCode.gmir GMIR.g_anyext)) (op.getResultTypes! ctx.raw)
        operands bs mem regions) (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  simp only [CTree.interpretOp', GMIR.interpretOpCTree] at h
  split at h
  · next w val hOps =>
    split at h
    · next resType hRes =>
      split at h
      · next resBw hResBw =>
        split at h
        · simp only [CTree.MayReturn.fail_iff] at h
        · next hle =>
          simp only [CTree.tau_def, CTree.MayReturn.tauG_iff, CTree.ret_pure,
            CTree.MayReturn.pure_iff, Prod.mk.injEq] at h
          obtain ⟨msb, rfl, -, -⟩ := h
          have hc := GMIR.interpretOp'_results_conform .g_anyext (bs := bs) (mem := mem)
            (mem' := mem) (act := none) hType hV hConf
            (by simp only [GMIR.interpretOp', hOps, hRes, hResBw, hle, Interp.pure_eq,
              ↓reduceDIte]; rfl)
          exact arrayConforms_int_congr hc
      · simp only [CTree.MayReturn.fail_iff] at h
    · simp only [CTree.MayReturn.fail_iff] at h
  · simp only [CTree.MayReturn.fail_iff] at h

/-- Every result the CTree of a verified `g_load` can produce conforms to its result type. -/
private theorem load_results_conform {ctx : WfIRContext OpCode} {op : OperationPtr}
    {opIn : op.InBounds ctx.raw} {operands vals : Array RuntimeValue} {mem mem' : MemoryState}
    {act : Option ControlFlowAction} {bs : Array BlockPtr} {regions : Array RegionPtr}
    (hType : op.getOpType! ctx.raw = .gmir .g_load) (hV : op.Verified ctx opIn)
    (hConf : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : CTree.MayReturn
      (CTree.interpretOp' (.gmir .g_load)
        (op.getProperties! ctx.raw (OpCode.gmir GMIR.g_load)) (op.getResultTypes! ctx.raw)
        operands bs mem regions) (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  simp only [CTree.interpretOp', GMIR.interpretOpCTree, Bind.bind,
    CTree.MayReturn.bind_iff, CTree.MayReturn.monadLift_iff] at h
  obtain ⟨⟨results, mem₂, action⟩, hI, h⟩ := h
  have hc := GMIR.interpretOp'_results_conform .g_load hType hV hConf hI
  split at h
  · next w val hRes =>
    split at h
    · next hlt =>
      simp only [CTree.tau_def, CTree.MayReturn.tauG_iff, CTree.ret_pure,
        CTree.MayReturn.pure_iff, Prod.mk.injEq] at h
      obtain ⟨msb, rfl, -, -⟩ := h
      obtain rfl : results = #[.int w val] := List.eq_toArray_iff.mpr hRes
      exact arrayConforms_int_congr hc
    · simp only [CTree.MayReturn.pure_iff, Prod.mk.injEq] at h
      obtain ⟨rfl, -, -⟩ := h
      exact hc
  · simp only [CTree.MayReturn.pure_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, -, -⟩ := h
    exact hc

/-- The results of a CTree run of every gMIR opcode conform to their types. -/
theorem OpCode.resultsConform_gmir (opT : GMIR) : OpCode.ResultsConform (.gmir opT) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType hV operands mem hConf vals mem' act h => ?_
  have hType! : op.getOpType! ctx.raw = .gmir opT := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  rw [OperationPtr.interpretCTree_def!, hType!] at h
  by_cases h₁ : opT = .g_anyext
  · subst h₁; exact anyext_results_conform hType! hV hConf h
  by_cases h₂ : opT = .g_load
  · subst h₂; exact load_results_conform hType! hV hConf h
  by_cases h₃ : opT = .g_freeze
  · subst h₃; exact freeze_results_conform hType! hV hConf h
  · rw [gmir_interpretOp'_ctree_eq_lift h₁ h₂ h₃,
      CTree.MayReturn.monadLift_iff] at h
    simp only [Veir.interpretOp'] at h
    exact GMIR.interpretOp'_results_conform opT hType! hV hConf h

instance (op : GMIR) : ResultsConform (.gmir op) := ⟨OpCode.resultsConform_gmir op⟩

end Veir

end
