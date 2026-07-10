import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.LLVM.Int.Bitblast
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Data.Refinement
import Veir.Passes.InstructionSelection.Proofs
import Veir.Passes.InstructionSelection.RISCV64
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerConst
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSlti

namespace Veir

/-!
## Correctness of `icmp_local`

`icmp_local` lowers `llvm.icmp` on `i64`/`i32`/`i8` operands to a RISC-V comparison sequence. Every
arm shares the prologue `icmpCastExtLocal` (cast both operands into registers, sign-extending them
for the narrow widths) and the epilogue `replaceWithRegLocal` (cast the `i1` result back); the five
possible comparison sequences in between are the `icmpEmit*Local` combinators.

The proof mirrors that factoring:

* `icmpCastExtLocal_mono` transports in-bounds, type and dominance facts across the prologue's
  creations, and `icmpCastExtLocal_run` symbolically executes the prologue, producing the two
  comparison registers `e (toReg xt)` / `e (toReg yt)` for refinements `xt`/`yt` of the source
  operands. Both are stated against an arbitrary *final* context `F` reached from the prologue's
  context by further creations, which the caller supplies as generic transport hypotheses
  (`hTransOp`/`hTransDom`) — this is what lets the prologue be proven once instead of once per arm.
* One `icmpEmit*Local_sound` lemma per comparison sequence peels its own creations, discharges the
  transport hypotheses from them, replays the prologue through `interpretOpList_append`, and then
  executes its own ops.
* `icmp_local_preservesSemantics` peels the matcher and the width guards and dispatches the twelve
  predicate arms onto those five lemmas, each with its data-level refinement lemma.
-/


/-! ### Context extension

Every arm creates its operations on top of the prologue's context `ctxP`, so the prologue's
structural facts have to be transported into the arm's final context. `CtxExtends op ctx ctx'`
bundles exactly what a chain of `WfRewriter.createOp`s preserves, and is closed under composition;
this is what lets the prologue be proven once, against an arbitrary final context, instead of once
per arm. -/

/-- The facts preserved when `ctx'` is reached from `ctx` by creating fresh (detached) operations:
    everything already in bounds keeps its in-bounds status, opcode, operands, result types, value
    types, and its dominance of the program point before `op`. -/
structure CtxExtends (op : OperationPtr) (ctx ctx' : WfIRContext OpCode) : Prop where
  /-- Pre-existing operations stay in bounds. -/
  inBounds : ∀ o : OperationPtr, o.InBounds ctx.raw → o.InBounds ctx'.raw
  /-- Pre-existing operations keep their opcode. -/
  opType : ∀ o : OperationPtr, o.InBounds ctx.raw → o.getOpType! ctx'.raw = o.getOpType! ctx.raw
  /-- Pre-existing operations keep their operands. -/
  operands : ∀ o : OperationPtr, o.InBounds ctx.raw →
    o.getOperands! ctx'.raw = o.getOperands! ctx.raw
  /-- Pre-existing operations keep their result types. -/
  resultTypes : ∀ o : OperationPtr, o.InBounds ctx.raw →
    o.getResultTypes! ctx'.raw = o.getResultTypes! ctx.raw
  /-- Pre-existing operations keep their properties (at every opcode). -/
  properties : ∀ o : OperationPtr, o.InBounds ctx.raw → ∀ oc : OpCode,
    o.getProperties! ctx'.raw oc = o.getProperties! ctx.raw oc
  /-- Pre-existing values stay in bounds. -/
  valueInBounds : ∀ v : ValuePtr, v.InBounds ctx.raw → v.InBounds ctx'.raw
  /-- Pre-existing values keep their type. -/
  valueType : ∀ v : ValuePtr, v.InBounds ctx.raw → v.getType! ctx'.raw = v.getType! ctx.raw
  /-- Dominance of the rewrite point is preserved. -/
  dominates : ∀ v : ValuePtr, v.dominatesIp (InsertPoint.before op) ctx →
    v.dominatesIp (InsertPoint.before op) ctx'

theorem CtxExtends.refl {op : OperationPtr} {ctx : WfIRContext OpCode} : CtxExtends op ctx ctx :=
  ⟨fun _ h => h, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ h => h,
    fun _ _ => rfl, fun _ h => h⟩

theorem CtxExtends.trans {op : OperationPtr} {ctx ctx' ctx'' : WfIRContext OpCode}
    (h₁ : CtxExtends op ctx ctx') (h₂ : CtxExtends op ctx' ctx'') : CtxExtends op ctx ctx'' where
  inBounds o ho := h₂.inBounds o (h₁.inBounds o ho)
  opType o ho := by rw [h₂.opType o (h₁.inBounds o ho), h₁.opType o ho]
  operands o ho := by rw [h₂.operands o (h₁.inBounds o ho), h₁.operands o ho]
  resultTypes o ho := by rw [h₂.resultTypes o (h₁.inBounds o ho), h₁.resultTypes o ho]
  properties o ho oc := by rw [h₂.properties o (h₁.inBounds o ho) oc, h₁.properties o ho oc]
  valueInBounds v hv := h₂.valueInBounds v (h₁.valueInBounds v hv)
  valueType v hv := by rw [h₂.valueType v (h₁.valueInBounds v hv), h₁.valueType v hv]
  dominates v hd := h₂.dominates v (h₁.dominates v hd)

/-- Creating one fresh operation extends the context. -/
theorem CtxExtends.of_createOp {ctx ctx' : WfIRContext OpCode} {op newOp : OperationPtr}
    {opType : OpCode} {resultTypes operands blockOperands regions}
    {properties : HasOpInfo.propertiesOf opType} {hoper hblock hreg hins}
    (h : WfRewriter.createOp ctx opType resultTypes operands blockOperands regions properties none
      hoper hblock hreg hins = some (ctx', newOp))
    (hop : op.InBounds ctx.raw) : CtxExtends op ctx ctx' := by
  have hFresh : ¬ newOp.InBounds ctx.raw := WfRewriter.createOp_new_not_inBounds newOp h
  have hne : ∀ o : OperationPtr, o.InBounds ctx.raw → o ≠ newOp := by grind
  refine ⟨fun o ho => WfRewriter.createOp_inBounds_mono (ptr := .operation o) h ho, ?_, ?_, ?_, ?_,
    fun v hv => WfRewriter.createOp_inBounds_mono (ptr := .value v) h hv, ?_,
    fun v hd => (ValuePtr.dominatesIp_before_WfRewriter_createOp h hop (hne op hop)).mpr hd⟩
  · intro o ho
    rw [OperationPtr.getOpType!_WfRewriter_createOp h, if_neg (hne o ho)]
  · intro o ho
    rw [OperationPtr.getOperands!_WfRewriter_createOp h, if_neg (hne o ho)]
  · intro o ho
    rw [OperationPtr.getResultTypes!_WfRewriter_createOp h, if_neg (hne o ho)]
  · intro o ho oc
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne h (hne o ho)]
  · intro v hv
    cases v with
    | blockArgument ba => rw [ValuePtr.getType!_WfRewriter_createOp h]
    | opResult opRes =>
      have hnd : ¬ (opRes.op = newOp ∧ opRes.index < resultTypes.size) := by
        rintro ⟨rfl, -⟩
        exact hFresh (by grind [ValuePtr.InBounds, OpResultPtr.InBounds])
      rw [ValuePtr.getType!_WfRewriter_createOp h]
      simp only [hnd, dif_neg, not_false_eq_true]


/-! ### The shared prologue `icmpCastExtLocal` -/

/-- The prologue only creates fresh operations, so it extends the context. -/
theorem icmpCastExtLocal_extends {ctx ctxP : WfIRContext OpCode} {op : OperationPtr}
    {lhs rhs a b : ValuePtr} {ext : Option IcmpExtOp} {pre : Array OperationPtr}
    (opInBounds : op.InBounds ctx.raw)
    (hCE : icmpCastExtLocal ctx lhs rhs ext = some (ctxP, pre, a, b)) :
    CtxExtends op ctx ctxP := by
  simp only [icmpCastExtLocal, bind] at hCE
  peelOpCreation hCE ctx₁ lcastOp hLCast
  simp only [castToRegLocal] at hLCast
  replace hLCast := WfRewriter.createOp!_none_some hLCast
  obtain ⟨_, _, _, hLCast⟩ := hLCast
  peelOpCreation hCE ctx₂ rcastOp hRCast
  simp only [castToRegLocal] at hRCast
  replace hRCast := WfRewriter.createOp!_none_some hRCast
  obtain ⟨_, _, _, hRCast⟩ := hRCast
  have E₁ := CtxExtends.of_createOp hLCast opInBounds
  have E₂ := CtxExtends.of_createOp hRCast (E₁.inBounds op opInBounds)
  have E₁₂ := E₁.trans E₂
  split at hCE
  · obtain ⟨rfl, -, -, -⟩ := by simpa using hCE
    exact E₁₂
  · peelOpCreation hCE ctx₃ lsOp hLs
    replace hLs := WfRewriter.createOp!_none_some hLs
    obtain ⟨_, _, _, hLs⟩ := hLs
    peelOpCreation hCE ctx₄ rsOp hRs
    replace hRs := WfRewriter.createOp!_none_some hRs
    obtain ⟨_, _, _, hRs⟩ := hRs
    obtain ⟨rfl, -, -, -⟩ := by simpa using hCE
    have E₃ := CtxExtends.of_createOp hLs (E₁₂.inBounds op opInBounds)
    have E₄ := CtxExtends.of_createOp hRs (E₃.inBounds op (E₁₂.inBounds op opInBounds))
    exact E₁₂.trans (E₃.trans E₄)

/-- The prologue's two comparison registers are in bounds in the context it returns. -/
theorem icmpCastExtLocal_regs_inBounds {ctx ctxP : WfIRContext OpCode}
    {lhs rhs a b : ValuePtr} {ext : Option IcmpExtOp} {pre : Array OperationPtr}
    (hCE : icmpCastExtLocal ctx lhs rhs ext = some (ctxP, pre, a, b)) :
    a.InBounds ctxP.raw ∧ b.InBounds ctxP.raw := by
  rcases ext with _ | eo
  all_goals
    simp only [icmpCastExtLocal, bind] at hCE
    peelOpCreation hCE ctx₁ lcastOp hLCast
    simp only [castToRegLocal] at hLCast
    replace hLCast := WfRewriter.createOp!_none_some hLCast
    obtain ⟨_, _, _, hLCast⟩ := hLCast
    peelOpCreation hCE ctx₂ rcastOp hRCast
    simp only [castToRegLocal] at hRCast
    replace hRCast := WfRewriter.createOp!_none_some hRCast
    obtain ⟨_, _, _, hRCast⟩ := hRCast
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa using hCE
    have E₂ := CtxExtends.of_createOp (op := lcastOp) hRCast
      (WfRewriter.createOp_new_inBounds _ hLCast)
    exact ⟨E₂.valueInBounds _ (by grind [ValuePtr.InBounds, OpResultPtr.InBounds,
        OperationPtr.getResult]),
      by grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]⟩
  · peelOpCreation hCE ctx₃ lsOp hLs
    replace hLs := WfRewriter.createOp!_none_some hLs
    obtain ⟨_, _, _, hLs⟩ := hLs
    peelOpCreation hCE ctx₄ rsOp hRs
    replace hRs := WfRewriter.createOp!_none_some hRs
    obtain ⟨_, _, _, hRs⟩ := hRs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa using hCE
    have E₄ := CtxExtends.of_createOp (op := lsOp) hRs (WfRewriter.createOp_new_inBounds _ hLs)
    exact ⟨E₄.valueInBounds _ (by grind [ValuePtr.InBounds, OpResultPtr.InBounds,
        OperationPtr.getResult]),
      by grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]⟩

/-- Symbolic execution of the prologue in the arm's final context `F`: the two casts (and, when
    `ext` fires, the two sign-extensions) run without touching memory and leave the comparison
    registers holding `e (toReg xt)` and `e (toReg yt)`, where `e` is the extension's semantics
    (the identity when there is none).

    The arm supplies `hExt`, the extension of `ctxP` to its own final context, which is how this
    single lemma serves every arm. -/
theorem icmpCastExtLocal_run {ctx ctxP F : WfIRContext OpCode} {op : OperationPtr}
    {lhs rhs a b : ValuePtr} {ext : Option IcmpExtOp} {pre : Array OperationPtr}
    {e : Data.RISCV.Reg → Data.RISCV.Reg} {bw : Nat} {xt yt : Data.LLVM.Int bw}
    {state' : InterpreterState F}
    (opInBounds : op.InBounds ctx.raw)
    (hCE : icmpCastExtLocal ctx lhs rhs ext = some (ctxP, pre, a, b))
    (hExt : CtxExtends op ctxP F)
    (hExtId : ext = none → ∀ r, e r = r)
    (hExtSem : ∀ eo, ext = some eo → ∀ (props : HasDialectOpInfo.propertiesOf eo.op)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (r : Data.RISCV.Reg),
        Riscv.interpretOp' eo.op props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (e r)], mem, none)))
    (hRhsIn : rhs.InBounds ctx.raw)
    (hLVal : state'.variables.getVar? lhs = some (RuntimeValue.int bw xt))
    (hRVal : state'.variables.getVar? rhs = some (RuntimeValue.int bw yt))
    (hin : ∀ o ∈ pre.toList, o.InBounds F.raw) :
    ∃ sPre : InterpreterState F,
      interpretOpList pre.toList state' hin = some (.ok (sPre, none)) ∧
      sPre.memory = state'.memory ∧
      sPre.variables.getVar? a = some (.reg (e (LLVM.Int.toReg xt))) ∧
      sPre.variables.getVar? b = some (.reg (e (LLVM.Int.toReg yt))) := by
  -- The two casts are peeled the same way in both branches.
  rcases ext with _ | eo
  all_goals
    simp only [icmpCastExtLocal, bind] at hCE
    peelOpCreation hCE ctx₁ lcastOp hLCast
    simp only [castToRegLocal] at hLCast
    replace hLCast := WfRewriter.createOp!_none_some hLCast
    obtain ⟨_, _, _, hLCast⟩ := hLCast
    peelOpCreation hCE ctx₂ rcastOp hRCast
    simp only [castToRegLocal] at hRCast
    replace hRCast := WfRewriter.createOp!_none_some hRCast
    obtain ⟨_, _, _, hRCast⟩ := hRCast
    have E₁ := CtxExtends.of_createOp hLCast opInBounds
    have E₂ := CtxExtends.of_createOp hRCast (E₁.inBounds op opInBounds)
    have hLCastIn₁ : lcastOp.InBounds ctx₁.raw := WfRewriter.createOp_new_inBounds _ hLCast
    have hRCastIn₂ : rcastOp.InBounds ctx₂.raw := WfRewriter.createOp_new_inBounds _ hRCast
    have hLCastFresh : ¬ lcastOp.InBounds ctx.raw := WfRewriter.createOp_new_not_inBounds _ hLCast
    have hRCastFresh₁ : ¬ rcastOp.InBounds ctx₁.raw :=
      WfRewriter.createOp_new_not_inBounds _ hRCast
    have hLResIn₁ : (ValuePtr.opResult (lcastOp.getResult 0)).InBounds ctx₁.raw := by
      grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  · -- ===== no sign-extension (`i64`): the two casts are the whole prologue =====
    obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa using hCE
    have F₂ : CtxExtends op ctx₂ F := hExt
    have F₁ : CtxExtends op ctx₁ F := E₂.trans hExt
    have hLCastType : lcastOp.getOpType! F.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType lcastOp hLCastIn₁]; grind
    have hLCastOperands : lcastOp.getOperands! F.raw = #[lhs] := by
      rw [F₁.operands lcastOp hLCastIn₁]; grind
    have hLCastResTypes :
        lcastOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes lcastOp hLCastIn₁]; grind
    have hRCastType : rcastOp.getOpType! F.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType rcastOp hRCastIn₂]; grind
    have hRCastOperands : rcastOp.getOperands! F.raw = #[rhs] := by
      rw [F₂.operands rcastOp hRCastIn₂]; grind
    have hRCastResTypes :
        rcastOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes rcastOp hRCastIn₂]; grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := hin lcastOp (by simp))
        hLCastType hLCastOperands hLCastResTypes hLVal
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int bw yt) := by
      rw [hFrame₁ rhs (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hRhsIn hLCastFresh)]
      exact hRVal
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := hin rcastOp (by simp))
        hRCastType hRCastOperands hRCastResTypes hRVal₁
    refine ⟨s₂, ?_, by grind, ?_, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, Interp]
    · rw [hFrame₂ _
        (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hLResIn₁ hRCastFresh₁), hRes₁,
        hExtId rfl]
    · rw [hRes₂, hExtId rfl]
  · -- ===== sign-extended prologue (`i32`/`i8`) =====
    peelOpCreation hCE ctx₃ lsOp hLs
    replace hLs := WfRewriter.createOp!_none_some hLs
    obtain ⟨_, _, _, hLs⟩ := hLs
    peelOpCreation hCE ctx₄ rsOp hRs
    replace hRs := WfRewriter.createOp!_none_some hRs
    obtain ⟨_, _, _, hRs⟩ := hRs
    obtain ⟨rfl, rfl, rfl, rfl⟩ := by simpa using hCE
    have E₃ := CtxExtends.of_createOp hLs (E₂.inBounds op (E₁.inBounds op opInBounds))
    have E₄ := CtxExtends.of_createOp hRs
      (E₃.inBounds op (E₂.inBounds op (E₁.inBounds op opInBounds)))
    have F₄ : CtxExtends op ctx₄ F := hExt
    have F₃ : CtxExtends op ctx₃ F := E₄.trans hExt
    have F₂ : CtxExtends op ctx₂ F := E₃.trans F₃
    have F₁ : CtxExtends op ctx₁ F := E₂.trans F₂
    have hLsIn₃ : lsOp.InBounds ctx₃.raw := WfRewriter.createOp_new_inBounds _ hLs
    have hRsIn₄ : rsOp.InBounds ctx₄.raw := WfRewriter.createOp_new_inBounds _ hRs
    have hLsFresh₂ : ¬ lsOp.InBounds ctx₂.raw := WfRewriter.createOp_new_not_inBounds _ hLs
    have hRsFresh₃ : ¬ rsOp.InBounds ctx₃.raw := WfRewriter.createOp_new_not_inBounds _ hRs
    have hRResIn₂ : (ValuePtr.opResult (rcastOp.getResult 0)).InBounds ctx₂.raw := by
      grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
    have hLsResIn₃ : (ValuePtr.opResult (lsOp.getResult 0)).InBounds ctx₃.raw := by
      grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
    have hLCastType : lcastOp.getOpType! F.raw = .builtin .unrealized_conversion_cast := by
      rw [F₁.opType lcastOp hLCastIn₁]; grind
    have hLCastOperands : lcastOp.getOperands! F.raw = #[lhs] := by
      rw [F₁.operands lcastOp hLCastIn₁]; grind
    have hLCastResTypes :
        lcastOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₁.resultTypes lcastOp hLCastIn₁]; grind
    have hRCastType : rcastOp.getOpType! F.raw = .builtin .unrealized_conversion_cast := by
      rw [F₂.opType rcastOp hRCastIn₂]; grind
    have hRCastOperands : rcastOp.getOperands! F.raw = #[rhs] := by
      rw [F₂.operands rcastOp hRCastIn₂]; grind
    have hRCastResTypes :
        rcastOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₂.resultTypes rcastOp hRCastIn₂]; grind
    have hLsType : lsOp.getOpType! F.raw = .riscv eo.op := by
      rw [F₃.opType lsOp hLsIn₃]; grind
    have hLsOperands : lsOp.getOperands! F.raw = #[ValuePtr.opResult (lcastOp.getResult 0)] := by
      rw [F₃.operands lsOp hLsIn₃]; grind
    have hLsResTypes : lsOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₃.resultTypes lsOp hLsIn₃]; grind
    have hRsType : rsOp.getOpType! F.raw = .riscv eo.op := by
      rw [F₄.opType rsOp hRsIn₄]; grind
    have hRsOperands : rsOp.getOperands! F.raw = #[ValuePtr.opResult (rcastOp.getResult 0)] := by
      rw [F₄.operands rsOp hRsIn₄]; grind
    have hRsResTypes : rsOp.getResultTypes! F.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      rw [F₄.resultTypes rsOp hRsIn₄]; grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, hFrame₁⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := hin lcastOp (by simp))
        hLCastType hLCastOperands hLCastResTypes hLVal
    have hRVal₁ : s₁.variables.getVar? rhs = some (RuntimeValue.int bw yt) := by
      rw [hFrame₁ rhs (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hRhsIn hLCastFresh)]
      exact hRVal
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, hFrame₂⟩ :=
      interpretOp_castToReg_forward (state := s₁) (inBounds := hin rcastOp (by simp))
        hRCastType hRCastOperands hRCastResTypes hRVal₁
    have hLRes₂ : s₂.variables.getVar? (ValuePtr.opResult (lcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg xt)) := by
      rw [hFrame₂ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hLResIn₁ hRCastFresh₁)]
      exact hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, hFrame₃⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₂) (inBounds := hin lsOp (by simp)) (f := e)
        (fun props rt bo mem => hExtSem eo rfl props rt bo mem _)
        hLsType hLsOperands hLsResTypes hLRes₂
    have hRRes₃ : s₃.variables.getVar? (ValuePtr.opResult (rcastOp.getResult 0))
        = some (RuntimeValue.reg (LLVM.Int.toReg yt)) := by
      rw [hFrame₃ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hRResIn₂ hLsFresh₂)]
      exact hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, hFrame₄⟩ :=
      interpretOp_riscv_unaryReg_forward (state := s₃) (inBounds := hin rsOp (by simp)) (f := e)
        (fun props rt bo mem => hExtSem eo rfl props rt bo mem _)
        hRsType hRsOperands hRsResTypes hRRes₃
    refine ⟨s₄, ?_, by grind, ?_, hRes₄⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, Interp]
    · rw [hFrame₄ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hLsResIn₃ hRsFresh₃)]
      exact hRes₃


/-! ### The comparison arms

Each arm peels its own creations, builds the `CtxExtends ctxP newCtx` witness they justify, replays
the prologue with `icmpCastExtLocal_run` through `interpretOpList_append`, and then executes its own
operations. The per-predicate content is entirely in `hData`. -/

set_option maxHeartbeats 1600000 in
/-- Correctness of the single-comparison arm (`slt`/`sgt`/`ult`/`ugt`). -/
theorem icmpEmitCmpLocal_sound {ctx : WfIRContext OpCode} {op : OperationPtr}
    (opInBounds : op.InBounds ctx.raw)
    {lhs rhs : ValuePtr} {ext : Option IcmpExtOp} {rop : Riscv}
    {hrop : Riscv.propertiesOf rop = Unit} {swap : Bool}
    {e : Data.RISCV.Reg → Data.RISCV.Reg} {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg}
    {pattern : LocalRewritePattern OpCode}
    {hReturnOps : pattern.ReturnOps} {hReturnCtx : pattern.ReturnCtxChanges}
    {hReturnVIB : pattern.ReturnValuesInBounds} {hReturnV : pattern.ReturnValues}
    {newCtx : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {state newState : InterpreterState ctx} {state' : InterpreterState newCtx}
    {bw : Nat} {xVal yVal : Data.LLVM.Int bw} {srcVal : Data.LLVM.Int 1}
    {ipIn : (InsertPoint.before op).InBounds ctx.raw}
    {ipIn' : (InsertPoint.before op).InBounds newCtx.raw}
    (hpatternOrig : pattern ctx op = some (newCtx, some (newOps, newValues)))
    (hEmit : icmpEmitCmpLocal ctx op lhs rhs ext rop hrop swap
      = some (newCtx, some (newOps, newValues)))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩)
    (hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw)
    (hLhsIn : lhs.InBounds ctx.raw) (hRhsIn : rhs.InBounds ctx.raw)
    (hxVal : state.variables.getVar? lhs = some (RuntimeValue.int bw xVal))
    (hyVal : state.variables.getVar? rhs = some (RuntimeValue.int bw yVal))
    (hMem : state.memory = newState.memory)
    (memoryRefinement : state.memory = state'.memory)
    (hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx)
    (hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx)
    (lNotOp : lhs ∉ op.getResults! ctx.raw) (rNotOp : rhs ∉ op.getResults! ctx.raw)
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) ipIn')
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpatternOrig hReturnVIB hReturnV hReturnCtx)
      (.at (.before op)) (.at (.before op)) ipIn ipIn')
    (hExtId : ext = none → ∀ r, e r = r)
    (hExtSem : ∀ eo, ext = some eo → ∀ (props : HasDialectOpInfo.propertiesOf eo.op)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (r : Data.RISCV.Reg),
        Riscv.interpretOp' eo.op props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (e r)], mem, none)))
    (hSemR : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf rop)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f r₁ r₂)], mem, none)))
    (hData : ∀ xt yt : Data.LLVM.Int bw, xVal ⊒ xt → yVal ⊒ yt →
      srcVal ⊒ RISCV.Reg.toInt
        (f (if swap then e (LLVM.Int.toReg yt) else e (LLVM.Int.toReg xt))
           (if swap then e (LLVM.Int.toReg xt) else e (LLVM.Int.toReg yt))) 1) :
    ∃ newState', interpretOpList newOps.toList state'
        (by grind [LocalRewritePattern.ReturnOps]) = some (newState', none) ∧
      newState.memory = newState'.memory ∧
      ∃ targetValues, newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
        (#[RuntimeValue.int 1 srcVal] : Array RuntimeValue) ⊒ targetValues := by
  -- Peel the prologue (opaquely) and this arm's two creations.
  simp only [icmpEmitCmpLocal, bind, Option.bind_eq_some_iff] at hEmit
  obtain ⟨⟨ctxP, pre, a, b⟩, hCE, hEmit⟩ := hEmit
  obtain ⟨u, v, huv⟩ : ∃ u v, (if swap then (b, a) else (a, b)) = (u, v) := ⟨_, _, rfl⟩
  rw [huv] at hEmit
  obtain ⟨⟨ctx₅, cmpOp⟩, hCmp, hEmit⟩ := hEmit
  replace hCmp := WfRewriter.createOp!_none_some hCmp
  obtain ⟨_, _, _, hCmp⟩ := hCmp
  obtain ⟨⟨ctx₆, castBackOp⟩, hCastBack, hEmit⟩ := hEmit
  simp only [replaceWithRegLocal] at hCastBack
  replace hCastBack := WfRewriter.createOp!_none_some hCastBack
  obtain ⟨_, _, _, hCastBack⟩ := hCastBack
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hEmit
  -- Context extensions: prologue, then this arm's two creations.
  have Ep := icmpCastExtLocal_extends opInBounds hCE
  have hOpInP : op.InBounds ctxP.raw := Ep.inBounds op opInBounds
  have E₅ := CtxExtends.of_createOp hCmp hOpInP
  have E₆ := CtxExtends.of_createOp hCastBack (E₅.inBounds op hOpInP)
  have hExtP : CtxExtends op ctxP ctx₆ := E₅.trans E₆
  have Ectx : CtxExtends op ctx ctx₆ := Ep.trans hExtP
  -- All emitted ops are in bounds in the final context.
  have hOpsIn : ∀ o ∈ (pre ++ #[cmpOp, castBackOp]).toList, o.InBounds ctx₆.raw := by
    grind [LocalRewritePattern.ReturnOps]
  have hPreIn : ∀ o ∈ pre.toList, o.InBounds ctx₆.raw := by
    intro o ho
    exact hOpsIn o (by simp only [Array.toList_append, List.mem_append]; exact Or.inl ho)
  -- Read the refined operands in the target state.
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL (Ectx.dominates lhs hDomCtxL) lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR (Ectx.dominates rhs hDomCtxR) rNotOp
  -- Replay the prologue.
  obtain ⟨sPre, hPre, hPreMem, hAVal, hBVal⟩ :=
    icmpCastExtLocal_run opInBounds hCE hExtP hExtId hExtSem hRhsIn hLVal' hRVal' hPreIn
  -- The two comparison operands, in the order this arm feeds them to `rop`.
  have hUVal : sPre.variables.getVar? u
      = some (.reg (if swap then e (LLVM.Int.toReg yt) else e (LLVM.Int.toReg xt))) := by
    cases swap <;> (simp only [Bool.false_eq_true, reduceIte, Prod.mk.injEq] at huv ⊢
                    obtain ⟨rfl, rfl⟩ := huv) <;> assumption
  have hVVal : sPre.variables.getVar? v
      = some (.reg (if swap then e (LLVM.Int.toReg xt) else e (LLVM.Int.toReg yt))) := by
    cases swap <;> (simp only [Bool.false_eq_true, reduceIte, Prod.mk.injEq] at huv ⊢
                    obtain ⟨rfl, rfl⟩ := huv) <;> assumption
  -- Structural facts about this arm's two ops.
  have hCmpIn₅ : cmpOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hCmp
  have hCmpType : cmpOp.getOpType! ctx₆.raw = .riscv rop := by
    rw [E₆.opType cmpOp hCmpIn₅]; grind
  have hCmpOperands : cmpOp.getOperands! ctx₆.raw = #[u, v] := by
    rw [E₆.operands cmpOp hCmpIn₅]; grind
  have hCmpResTypes : cmpOp.getResultTypes! ctx₆.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [E₆.resultTypes cmpOp hCmpIn₅]; grind
  have hCastBackType : castBackOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (cmpOp.getResult 0)] := by grind
  have isT : Attribute.isType (Attribute.integerType (⟨1⟩ : IntegerType)) := by grind
  have hCBType : ((op.getResult 0).get! ctx₅.raw).type
      = (⟨Attribute.integerType ⟨1⟩, isT⟩ : TypeAttr) := by
    have h1 := (Ep.trans E₅).valueType (ValuePtr.opResult (op.getResult 0)) hResIn
    simp only [ValuePtr.getType!_opResult] at h1
    apply Subtype.ext
    rw [show ((op.getResult 0).get! ctx₅.raw).type = ((op.getResult 0).get! ctx.raw).type from h1]
    exact hResType
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.integerType ⟨1⟩, isT⟩] := by grind
  -- Execute this arm's two ops on top of the prologue's state.
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := sPre) (inBounds := hOpsIn cmpOp (by simp))
      (f := f) (hSemR _ _) hCmpType hCmpOperands hCmpResTypes hUVal hVVal
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
    interpretOp_castBack_forward (state := s₅) (inBounds := hOpsIn castBackOp (by simp))
      hCastBackType hCastBackOperands hCastBackResTypes hRes₅
  refine ⟨s₆, ?_, by grind, ?_⟩
  · simp only [Array.toList_append]
    rw [interpretOpList_append, hPre]
    simp [interpretOpList_cons, hI₅, hI₆, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt (f
        (if swap then e (LLVM.Int.toReg yt) else e (LLVM.Int.toReg xt))
        (if swap then e (LLVM.Int.toReg xt) else e (LLVM.Int.toReg yt))) 1)], ?_, ?_⟩
    · simp [hRes₆, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using hData xt yt hxtRef hytRef⟩

set_option maxHeartbeats 1600000 in
/-- Correctness of the comparison-then-immediate arm (`sle`/`sge`/`ule`/`uge` and the generic
    `eq`). -/
theorem icmpEmitCmpImmLocal_sound {ctx : WfIRContext OpCode} {op : OperationPtr}
    (opInBounds : op.InBounds ctx.raw)
    {lhs rhs : ValuePtr} {ext : Option IcmpExtOp}
    {e : Data.RISCV.Reg → Data.RISCV.Reg}
    {pattern : LocalRewritePattern OpCode}
    {hReturnOps : pattern.ReturnOps} {hReturnCtx : pattern.ReturnCtxChanges}
    {hReturnVIB : pattern.ReturnValuesInBounds} {hReturnV : pattern.ReturnValues}
    {newCtx : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {state newState : InterpreterState ctx} {state' : InterpreterState newCtx}
    {bw : Nat} {xVal yVal : Data.LLVM.Int bw} {srcVal : Data.LLVM.Int 1}
    {ipIn : (InsertPoint.before op).InBounds ctx.raw}
    {ipIn' : (InsertPoint.before op).InBounds newCtx.raw}
    (hpatternOrig : pattern ctx op = some (newCtx, some (newOps, newValues)))
    {rop : Riscv} {hrop : Riscv.propertiesOf rop = Unit} {swap : Bool}
    {ropImm : Riscv} {hropImm : Riscv.propertiesOf ropImm = RISCVImmediateProperties}
    {f : Data.RISCV.Reg → Data.RISCV.Reg → Data.RISCV.Reg} {g : Data.RISCV.Reg → Data.RISCV.Reg}
    (hEmit : icmpEmitCmpImmLocal ctx op lhs rhs ext rop hrop swap ropImm hropImm
      = some (newCtx, some (newOps, newValues)))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩)
    (hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw)
    (hLhsIn : lhs.InBounds ctx.raw) (hRhsIn : rhs.InBounds ctx.raw)
    (hxVal : state.variables.getVar? lhs = some (RuntimeValue.int bw xVal))
    (hyVal : state.variables.getVar? rhs = some (RuntimeValue.int bw yVal))
    (hMem : state.memory = newState.memory)
    (memoryRefinement : state.memory = state'.memory)
    (hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx)
    (hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx)
    (lNotOp : lhs ∉ op.getResults! ctx.raw) (rNotOp : rhs ∉ op.getResults! ctx.raw)
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) ipIn')
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpatternOrig hReturnVIB hReturnV hReturnCtx)
      (.at (.before op)) (.at (.before op)) ipIn ipIn')
    (hExtId : ext = none → ∀ r, e r = r)
    (hExtSem : ∀ eo, ext = some eo → ∀ (props : HasDialectOpInfo.propertiesOf eo.op)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (r : Data.RISCV.Reg),
        Riscv.interpretOp' eo.op props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (e r)], mem, none)))
    (hSemR : ∀ (r₁ r₂ : Data.RISCV.Reg) (props : HasDialectOpInfo.propertiesOf rop)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' rop props resultTypes #[.reg r₁, .reg r₂] blockOperands mem
          = some (.ok (#[.reg (f r₁ r₂)], mem, none)))
    (hSemImm : ∀ (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
        (blockOperands : Array BlockPtr) (mem : MemoryState),
        Riscv.interpretOp' ropImm (cast hropImm.symm icmpOneImm) resultTypes #[.reg r]
            blockOperands mem
          = some (.ok (#[.reg (g r)], mem, none)))
    (hData : ∀ xt yt : Data.LLVM.Int bw, xVal ⊒ xt → yVal ⊒ yt →
      srcVal ⊒ RISCV.Reg.toInt (g
        (f (if swap then e (LLVM.Int.toReg yt) else e (LLVM.Int.toReg xt))
           (if swap then e (LLVM.Int.toReg xt) else e (LLVM.Int.toReg yt)))) 1) :
    ∃ newState', interpretOpList newOps.toList state'
        (by grind [LocalRewritePattern.ReturnOps]) = some (newState', none) ∧
      newState.memory = newState'.memory ∧
      ∃ targetValues, newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
        (#[RuntimeValue.int 1 srcVal] : Array RuntimeValue) ⊒ targetValues := by
  simp only [icmpEmitCmpImmLocal, bind, Option.bind_eq_some_iff] at hEmit
  obtain ⟨⟨ctxP, pre, a, b⟩, hCE, hEmit⟩ := hEmit
  obtain ⟨u, v, huv⟩ : ∃ u v, (if swap then (b, a) else (a, b)) = (u, v) := ⟨_, _, rfl⟩
  rw [huv] at hEmit
  obtain ⟨⟨ctx₅, cmpOp⟩, hCmp, hEmit⟩ := hEmit
  replace hCmp := WfRewriter.createOp!_none_some hCmp
  obtain ⟨_, _, _, hCmp⟩ := hCmp
  obtain ⟨⟨ctx₆, immOp⟩, hImm, hEmit⟩ := hEmit
  replace hImm := WfRewriter.createOp!_none_some hImm
  obtain ⟨_, _, _, hImm⟩ := hImm
  obtain ⟨⟨ctx₇, castBackOp⟩, hCastBack, hEmit⟩ := hEmit
  simp only [replaceWithRegLocal] at hCastBack
  replace hCastBack := WfRewriter.createOp!_none_some hCastBack
  obtain ⟨_, _, _, hCastBack⟩ := hCastBack
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hEmit
  -- Context extensions: prologue, then this arm's creations.
  have Ep := icmpCastExtLocal_extends opInBounds hCE
  have hOpInP : op.InBounds ctxP.raw := Ep.inBounds op opInBounds
  have E₅ := CtxExtends.of_createOp hCmp hOpInP
  have E₆ := CtxExtends.of_createOp hImm (E₅.inBounds op hOpInP)
  have E₇ := CtxExtends.of_createOp hCastBack (E₆.inBounds op (E₅.inBounds op hOpInP))
  have hExtP : CtxExtends op ctxP ctx₇ := E₅.trans (E₆.trans E₇)
  have Ectx : CtxExtends op ctx ctx₇ := Ep.trans hExtP
  have hOpsIn : ∀ o ∈ (pre ++ #[cmpOp, immOp, castBackOp]).toList, o.InBounds ctx₇.raw := by
    grind [LocalRewritePattern.ReturnOps]
  have hPreIn : ∀ o ∈ pre.toList, o.InBounds ctx₇.raw := by
    intro o ho
    exact hOpsIn o (by simp only [Array.toList_append, List.mem_append]; exact Or.inl ho)
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL (Ectx.dominates lhs hDomCtxL) lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR (Ectx.dominates rhs hDomCtxR) rNotOp
  obtain ⟨sPre, hPre, hPreMem, hAVal, hBVal⟩ :=
    icmpCastExtLocal_run opInBounds hCE hExtP hExtId hExtSem hRhsIn hLVal' hRVal' hPreIn
  have hUVal : sPre.variables.getVar? u
      = some (.reg (if swap then e (LLVM.Int.toReg yt) else e (LLVM.Int.toReg xt))) := by
    cases swap <;> (simp only [Bool.false_eq_true, reduceIte, Prod.mk.injEq] at huv ⊢
                    obtain ⟨rfl, rfl⟩ := huv) <;> assumption
  have hVVal : sPre.variables.getVar? v
      = some (.reg (if swap then e (LLVM.Int.toReg xt) else e (LLVM.Int.toReg yt))) := by
    cases swap <;> (simp only [Bool.false_eq_true, reduceIte, Prod.mk.injEq] at huv ⊢
                    obtain ⟨rfl, rfl⟩ := huv) <;> assumption
  have hCmpIn₅ : cmpOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hCmp
  have hImmIn₆ : immOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds _ hImm
  have hCmpType : cmpOp.getOpType! ctx₇.raw = .riscv rop := by
    rw [(E₆.trans E₇).opType cmpOp hCmpIn₅]; grind
  have hCmpOperands : cmpOp.getOperands! ctx₇.raw = #[u, v] := by
    rw [(E₆.trans E₇).operands cmpOp hCmpIn₅]; grind
  have hCmpResTypes : cmpOp.getResultTypes! ctx₇.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [(E₆.trans E₇).resultTypes cmpOp hCmpIn₅]; grind
  have hImmType : immOp.getOpType! ctx₇.raw = .riscv ropImm := by
    rw [E₇.opType immOp hImmIn₆]; grind
  have hImmOperands : immOp.getOperands! ctx₇.raw = #[ValuePtr.opResult (cmpOp.getResult 0)] := by
    rw [E₇.operands immOp hImmIn₆]; grind
  have hImmResTypes : immOp.getResultTypes! ctx₇.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [E₇.resultTypes immOp hImmIn₆]; grind
  have hImmProps : immOp.getProperties! ctx₇.raw (.riscv ropImm)
      = cast hropImm.symm icmpOneImm := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hImm (operation := immOp)]
  have hCastBackType : castBackOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₇.raw = #[ValuePtr.opResult (immOp.getResult 0)] := by grind
  have isT : Attribute.isType (Attribute.integerType (⟨1⟩ : IntegerType)) := by grind
  have hCBType : ((op.getResult 0).get! ctx₆.raw).type
      = (⟨Attribute.integerType ⟨1⟩, isT⟩ : TypeAttr) := by
    have h1 := (Ep.trans (E₅.trans E₆)).valueType (ValuePtr.opResult (op.getResult 0)) hResIn
    simp only [ValuePtr.getType!_opResult] at h1
    apply Subtype.ext
    rw [show ((op.getResult 0).get! ctx₆.raw).type = ((op.getResult 0).get! ctx.raw).type from h1]
    exact hResType
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.integerType ⟨1⟩, isT⟩] := by grind
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := sPre) (inBounds := hOpsIn cmpOp (by simp))
      (f := f) (hSemR _ _) hCmpType hCmpOperands hCmpResTypes hUVal hVVal
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₅) (inBounds := hOpsIn immOp (by simp))
      (res := g _) (props := cast hropImm.symm icmpOneImm) (hSemImm _)
      hImmType hImmProps hImmOperands hImmResTypes hRes₅
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, -⟩ :=
    interpretOp_castBack_forward (state := s₆) (inBounds := hOpsIn castBackOp (by simp))
      hCastBackType hCastBackOperands hCastBackResTypes hRes₆
  refine ⟨s₇, ?_, by grind, ?_⟩
  · simp only [Array.toList_append]
    rw [interpretOpList_append, hPre]
    simp [interpretOpList_cons, hI₅, hI₆, hI₇, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt (g (f
        (if swap then e (LLVM.Int.toReg yt) else e (LLVM.Int.toReg xt))
        (if swap then e (LLVM.Int.toReg xt) else e (LLVM.Int.toReg yt)))) 1)], ?_, ?_⟩
    · simp [hRes₇, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa using hData xt yt hxtRef hytRef⟩

set_option maxHeartbeats 1600000 in
/-- Correctness of the `seqz` arm: `eq` against a zero constant lowers to `sltiu a 1`. -/
theorem icmpEmitSeqzLocal_sound {ctx : WfIRContext OpCode} {op : OperationPtr}
    (opInBounds : op.InBounds ctx.raw)
    {lhs rhs : ValuePtr} {ext : Option IcmpExtOp}
    {e : Data.RISCV.Reg → Data.RISCV.Reg}
    {pattern : LocalRewritePattern OpCode}
    {hReturnOps : pattern.ReturnOps} {hReturnCtx : pattern.ReturnCtxChanges}
    {hReturnVIB : pattern.ReturnValuesInBounds} {hReturnV : pattern.ReturnValues}
    {newCtx : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {state newState : InterpreterState ctx} {state' : InterpreterState newCtx}
    {bw : Nat} {xVal yVal : Data.LLVM.Int bw} {srcVal : Data.LLVM.Int 1}
    {ipIn : (InsertPoint.before op).InBounds ctx.raw}
    {ipIn' : (InsertPoint.before op).InBounds newCtx.raw}
    (hpatternOrig : pattern ctx op = some (newCtx, some (newOps, newValues)))
    (hEmit : icmpEmitSeqzLocal ctx op lhs rhs ext = some (newCtx, some (newOps, newValues)))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩)
    (hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw)
    (hLhsIn : lhs.InBounds ctx.raw) (hRhsIn : rhs.InBounds ctx.raw)
    (hxVal : state.variables.getVar? lhs = some (RuntimeValue.int bw xVal))
    (hyVal : state.variables.getVar? rhs = some (RuntimeValue.int bw yVal))
    (hMem : state.memory = newState.memory)
    (memoryRefinement : state.memory = state'.memory)
    (hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx)
    (hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx)
    (lNotOp : lhs ∉ op.getResults! ctx.raw) (rNotOp : rhs ∉ op.getResults! ctx.raw)
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) ipIn')
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpatternOrig hReturnVIB hReturnV hReturnCtx)
      (.at (.before op)) (.at (.before op)) ipIn ipIn')
    (hExtId : ext = none → ∀ r, e r = r)
    (hExtSem : ∀ eo, ext = some eo → ∀ (props : HasDialectOpInfo.propertiesOf eo.op)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (r : Data.RISCV.Reg),
        Riscv.interpretOp' eo.op props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (e r)], mem, none)))
    (hData : ∀ xt : Data.LLVM.Int bw, xVal ⊒ xt →
      srcVal ⊒ RISCV.Reg.toInt (Data.RISCV.sltiu (BitVec.ofInt 12 1) (e (LLVM.Int.toReg xt))) 1) :
    ∃ newState', interpretOpList newOps.toList state'
        (by grind [LocalRewritePattern.ReturnOps]) = some (newState', none) ∧
      newState.memory = newState'.memory ∧
      ∃ targetValues, newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
        (#[RuntimeValue.int 1 srcVal] : Array RuntimeValue) ⊒ targetValues := by
  simp only [icmpEmitSeqzLocal, bind, Option.bind_eq_some_iff] at hEmit
  obtain ⟨⟨ctxP, pre, a, b⟩, hCE, hEmit⟩ := hEmit
  obtain ⟨⟨ctx₅, immOp⟩, hImm, hEmit⟩ := hEmit
  replace hImm := WfRewriter.createOp!_none_some hImm
  obtain ⟨_, _, _, hImm⟩ := hImm
  obtain ⟨⟨ctx₆, castBackOp⟩, hCastBack, hEmit⟩ := hEmit
  simp only [replaceWithRegLocal] at hCastBack
  replace hCastBack := WfRewriter.createOp!_none_some hCastBack
  obtain ⟨_, _, _, hCastBack⟩ := hCastBack
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hEmit
  -- Context extensions: prologue, then this arm's creations.
  have Ep := icmpCastExtLocal_extends opInBounds hCE
  have hOpInP : op.InBounds ctxP.raw := Ep.inBounds op opInBounds
  have E₅ := CtxExtends.of_createOp hImm hOpInP
  have E₆ := CtxExtends.of_createOp hCastBack (E₅.inBounds op hOpInP)
  have hExtP : CtxExtends op ctxP ctx₆ := E₅.trans E₆
  have Ectx : CtxExtends op ctx ctx₆ := Ep.trans hExtP
  have hOpsIn : ∀ o ∈ (pre ++ #[immOp, castBackOp]).toList, o.InBounds ctx₆.raw := by
    grind [LocalRewritePattern.ReturnOps]
  have hPreIn : ∀ o ∈ pre.toList, o.InBounds ctx₆.raw := by
    intro o ho
    exact hOpsIn o (by simp only [Array.toList_append, List.mem_append]; exact Or.inl ho)
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL (Ectx.dominates lhs hDomCtxL) lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR (Ectx.dominates rhs hDomCtxR) rNotOp
  obtain ⟨sPre, hPre, hPreMem, hAVal, hBVal⟩ :=
    icmpCastExtLocal_run opInBounds hCE hExtP hExtId hExtSem hRhsIn hLVal' hRVal' hPreIn
  have hImmIn₅ : immOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hImm
  have hImmType : immOp.getOpType! ctx₆.raw = .riscv .sltiu := by
    rw [E₆.opType immOp hImmIn₅]; grind
  have hImmOperands : immOp.getOperands! ctx₆.raw = #[a] := by
    rw [E₆.operands immOp hImmIn₅]; grind
  have hImmResTypes : immOp.getResultTypes! ctx₆.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [E₆.resultTypes immOp hImmIn₅]; grind
  have hImmProps : immOp.getProperties! ctx₆.raw (.riscv .sltiu) = icmpOneImm := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hImm (operation := immOp)]
  have hCastBackType : castBackOp.getOpType! ctx₆.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₆.raw = #[ValuePtr.opResult (immOp.getResult 0)] := by grind
  have isT : Attribute.isType (Attribute.integerType (⟨1⟩ : IntegerType)) := by grind
  have hCBType : ((op.getResult 0).get! ctx₅.raw).type
      = (⟨Attribute.integerType ⟨1⟩, isT⟩ : TypeAttr) := by
    have h1 := (Ep.trans E₅).valueType (ValuePtr.opResult (op.getResult 0)) hResIn
    simp only [ValuePtr.getType!_opResult] at h1
    apply Subtype.ext
    rw [show ((op.getResult 0).get! ctx₅.raw).type = ((op.getResult 0).get! ctx.raw).type from h1]
    exact hResType
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₆.raw
      = #[⟨Attribute.integerType ⟨1⟩, isT⟩] := by grind
  have hSemImm : ∀ (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
      (blockOperands : Array BlockPtr) (mem : MemoryState),
      Riscv.interpretOp' .sltiu icmpOneImm resultTypes #[.reg r] blockOperands mem
        = some (.ok (#[.reg (Data.RISCV.sltiu (BitVec.ofInt 12 1) r)], mem, none)) := by
    intro r rt bo mem; simp [Riscv.interpretOp', icmpOneImm, pure, Interp]
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := sPre) (inBounds := hOpsIn immOp (by simp))
      (rop := Riscv.sltiu) (res := Data.RISCV.sltiu (BitVec.ofInt 12 1) (e (LLVM.Int.toReg xt)))
      (props := icmpOneImm) (hSemImm _) hImmType hImmProps hImmOperands hImmResTypes hAVal
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
    interpretOp_castBack_forward (state := s₅) (inBounds := hOpsIn castBackOp (by simp))
      hCastBackType hCastBackOperands hCastBackResTypes hRes₅
  refine ⟨s₆, ?_, by grind, ?_⟩
  · simp only [Array.toList_append]
    rw [interpretOpList_append, hPre]
    simp [interpretOpList_cons, hI₅, hI₆, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt
        (Data.RISCV.sltiu (BitVec.ofInt 12 1) (e (LLVM.Int.toReg xt))) 1)], ?_, ?_⟩
    · simp [hRes₆, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using hData xt hxtRef⟩

set_option maxHeartbeats 1600000 in
/-- Correctness of the `snez` arm: `ne` against a zero constant lowers to `sltu 0 a`. -/
theorem icmpEmitSnezLocal_sound {ctx : WfIRContext OpCode} {op : OperationPtr}
    (opInBounds : op.InBounds ctx.raw)
    {lhs rhs : ValuePtr} {ext : Option IcmpExtOp}
    {e : Data.RISCV.Reg → Data.RISCV.Reg}
    {pattern : LocalRewritePattern OpCode}
    {hReturnOps : pattern.ReturnOps} {hReturnCtx : pattern.ReturnCtxChanges}
    {hReturnVIB : pattern.ReturnValuesInBounds} {hReturnV : pattern.ReturnValues}
    {newCtx : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {state newState : InterpreterState ctx} {state' : InterpreterState newCtx}
    {bw : Nat} {xVal yVal : Data.LLVM.Int bw} {srcVal : Data.LLVM.Int 1}
    {ipIn : (InsertPoint.before op).InBounds ctx.raw}
    {ipIn' : (InsertPoint.before op).InBounds newCtx.raw}
    (hpatternOrig : pattern ctx op = some (newCtx, some (newOps, newValues)))
    (hEmit : icmpEmitSnezLocal ctx op lhs rhs ext = some (newCtx, some (newOps, newValues)))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩)
    (hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw)
    (hLhsIn : lhs.InBounds ctx.raw) (hRhsIn : rhs.InBounds ctx.raw)
    (hxVal : state.variables.getVar? lhs = some (RuntimeValue.int bw xVal))
    (hyVal : state.variables.getVar? rhs = some (RuntimeValue.int bw yVal))
    (hMem : state.memory = newState.memory)
    (memoryRefinement : state.memory = state'.memory)
    (hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx)
    (hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx)
    (lNotOp : lhs ∉ op.getResults! ctx.raw) (rNotOp : rhs ∉ op.getResults! ctx.raw)
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) ipIn')
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpatternOrig hReturnVIB hReturnV hReturnCtx)
      (.at (.before op)) (.at (.before op)) ipIn ipIn')
    (hExtId : ext = none → ∀ r, e r = r)
    (hExtSem : ∀ eo, ext = some eo → ∀ (props : HasDialectOpInfo.propertiesOf eo.op)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (r : Data.RISCV.Reg),
        Riscv.interpretOp' eo.op props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (e r)], mem, none)))
    (hData : ∀ xt : Data.LLVM.Int bw, xVal ⊒ xt →
      srcVal ⊒ RISCV.Reg.toInt
        (Data.RISCV.sltu (e (LLVM.Int.toReg xt)) (Data.RISCV.li (BitVec.ofInt 64 0))) 1) :
    ∃ newState', interpretOpList newOps.toList state'
        (by grind [LocalRewritePattern.ReturnOps]) = some (newState', none) ∧
      newState.memory = newState'.memory ∧
      ∃ targetValues, newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
        (#[RuntimeValue.int 1 srcVal] : Array RuntimeValue) ⊒ targetValues := by
  simp only [icmpEmitSnezLocal, bind, Option.bind_eq_some_iff] at hEmit
  obtain ⟨⟨ctxP, pre, a, b⟩, hCE, hEmit⟩ := hEmit
  obtain ⟨⟨ctx₅, liOp⟩, hLi, hEmit⟩ := hEmit
  replace hLi := WfRewriter.createOp!_none_some hLi
  obtain ⟨_, _, _, hLi⟩ := hLi
  obtain ⟨⟨ctx₆, cmpOp⟩, hCmp, hEmit⟩ := hEmit
  replace hCmp := WfRewriter.createOp!_none_some hCmp
  obtain ⟨_, _, _, hCmp⟩ := hCmp
  obtain ⟨⟨ctx₇, castBackOp⟩, hCastBack, hEmit⟩ := hEmit
  simp only [replaceWithRegLocal] at hCastBack
  replace hCastBack := WfRewriter.createOp!_none_some hCastBack
  obtain ⟨_, _, _, hCastBack⟩ := hCastBack
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hEmit
  -- Context extensions: prologue, then this arm's creations.
  have Ep := icmpCastExtLocal_extends opInBounds hCE
  have hOpInP : op.InBounds ctxP.raw := Ep.inBounds op opInBounds
  have E₅ := CtxExtends.of_createOp hLi hOpInP
  have E₆ := CtxExtends.of_createOp hCmp (E₅.inBounds op hOpInP)
  have E₇ := CtxExtends.of_createOp hCastBack (E₆.inBounds op (E₅.inBounds op hOpInP))
  have hExtP : CtxExtends op ctxP ctx₇ := E₅.trans (E₆.trans E₇)
  have Ectx : CtxExtends op ctx ctx₇ := Ep.trans hExtP
  have hOpsIn : ∀ o ∈ (pre ++ #[liOp, cmpOp, castBackOp]).toList, o.InBounds ctx₇.raw := by
    grind [LocalRewritePattern.ReturnOps]
  have hPreIn : ∀ o ∈ pre.toList, o.InBounds ctx₇.raw := by
    intro o ho
    exact hOpsIn o (by simp only [Array.toList_append, List.mem_append]; exact Or.inl ho)
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL (Ectx.dominates lhs hDomCtxL) lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR (Ectx.dominates rhs hDomCtxR) rNotOp
  obtain ⟨sPre, hPre, hPreMem, hAVal, hBVal⟩ :=
    icmpCastExtLocal_run opInBounds hCE hExtP hExtId hExtSem hRhsIn hLVal' hRVal' hPreIn
  have hLiIn₅ : liOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hLi
  have hLiFresh : ¬ liOp.InBounds ctxP.raw := WfRewriter.createOp_new_not_inBounds _ hLi
  have hCmpIn₆ : cmpOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds _ hCmp
  have hAInP : a.InBounds ctxP.raw := (icmpCastExtLocal_regs_inBounds hCE).1
  have hLiType : liOp.getOpType! ctx₇.raw = .riscv .li := by
    rw [(E₆.trans E₇).opType liOp hLiIn₅]; grind
  have hLiOperands : liOp.getOperands! ctx₇.raw = #[] := by
    rw [(E₆.trans E₇).operands liOp hLiIn₅]; grind
  have hLiResTypes : liOp.getResultTypes! ctx₇.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [(E₆.trans E₇).resultTypes liOp hLiIn₅]; grind
  have hLiProps : liOp.getProperties! ctx₇.raw (.riscv .li) = icmpZeroImm := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hCmp (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hLi (operation := liOp)]
  have hCmpType : cmpOp.getOpType! ctx₇.raw = .riscv .sltu := by
    rw [E₇.opType cmpOp hCmpIn₆]; grind
  have hCmpOperands : cmpOp.getOperands! ctx₇.raw = #[ValuePtr.opResult (liOp.getResult 0), a] := by
    rw [E₇.operands cmpOp hCmpIn₆]; grind
  have hCmpResTypes : cmpOp.getResultTypes! ctx₇.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [E₇.resultTypes cmpOp hCmpIn₆]; grind
  have hCastBackType : castBackOp.getOpType! ctx₇.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₇.raw = #[ValuePtr.opResult (cmpOp.getResult 0)] := by grind
  have isT : Attribute.isType (Attribute.integerType (⟨1⟩ : IntegerType)) := by grind
  have hCBType : ((op.getResult 0).get! ctx₆.raw).type
      = (⟨Attribute.integerType ⟨1⟩, isT⟩ : TypeAttr) := by
    have h1 := (Ep.trans (E₅.trans E₆)).valueType (ValuePtr.opResult (op.getResult 0)) hResIn
    simp only [ValuePtr.getType!_opResult] at h1
    apply Subtype.ext
    rw [show ((op.getResult 0).get! ctx₆.raw).type = ((op.getResult 0).get! ctx.raw).type from h1]
    exact hResType
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₇.raw
      = #[⟨Attribute.integerType ⟨1⟩, isT⟩] := by grind
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, hFrame₅⟩ :=
    interpretOp_riscv_li_forward (state := sPre) (inBounds := hOpsIn liOp (by simp))
      (props := icmpZeroImm) hLiType hLiProps hLiOperands hLiResTypes
  have hAVal₅ : s₅.variables.getVar? a = some (.reg (e (LLVM.Int.toReg xt))) := by
    rw [hFrame₅ a (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hAInP hLiFresh)]
    exact hAVal
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₅) (inBounds := hOpsIn cmpOp (by simp))
      (f := fun r₁ r₂ => Data.RISCV.sltu r₂ r₁) (fun _ _ _ _ => rfl)
      hCmpType hCmpOperands hCmpResTypes hRes₅ hAVal₅
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, -⟩ :=
    interpretOp_castBack_forward (state := s₆) (inBounds := hOpsIn castBackOp (by simp))
      hCastBackType hCastBackOperands hCastBackResTypes hRes₆
  refine ⟨s₇, ?_, by grind, ?_⟩
  · simp only [Array.toList_append]
    rw [interpretOpList_append, hPre]
    simp [interpretOpList_cons, hI₅, hI₆, hI₇, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt (Data.RISCV.sltu (e (LLVM.Int.toReg xt))
        (Data.RISCV.li (BitVec.ofInt 64 icmpZeroImm.value.value))) 1)], ?_, ?_⟩
    · simp [hRes₇, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa [icmpZeroImm] using hData xt hxtRef⟩

set_option maxHeartbeats 1600000 in
/-- Correctness of the generic `ne` arm: `sltu 0 (xor b a)`. -/
theorem icmpEmitXorSnezLocal_sound {ctx : WfIRContext OpCode} {op : OperationPtr}
    (opInBounds : op.InBounds ctx.raw)
    {lhs rhs : ValuePtr} {ext : Option IcmpExtOp}
    {e : Data.RISCV.Reg → Data.RISCV.Reg}
    {pattern : LocalRewritePattern OpCode}
    {hReturnOps : pattern.ReturnOps} {hReturnCtx : pattern.ReturnCtxChanges}
    {hReturnVIB : pattern.ReturnValuesInBounds} {hReturnV : pattern.ReturnValues}
    {newCtx : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {state newState : InterpreterState ctx} {state' : InterpreterState newCtx}
    {bw : Nat} {xVal yVal : Data.LLVM.Int bw} {srcVal : Data.LLVM.Int 1}
    {ipIn : (InsertPoint.before op).InBounds ctx.raw}
    {ipIn' : (InsertPoint.before op).InBounds newCtx.raw}
    (hpatternOrig : pattern ctx op = some (newCtx, some (newOps, newValues)))
    (hEmit : icmpEmitXorSnezLocal ctx op lhs rhs ext = some (newCtx, some (newOps, newValues)))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩)
    (hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw)
    (hLhsIn : lhs.InBounds ctx.raw) (hRhsIn : rhs.InBounds ctx.raw)
    (hxVal : state.variables.getVar? lhs = some (RuntimeValue.int bw xVal))
    (hyVal : state.variables.getVar? rhs = some (RuntimeValue.int bw yVal))
    (hMem : state.memory = newState.memory)
    (memoryRefinement : state.memory = state'.memory)
    (hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx)
    (hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx)
    (lNotOp : lhs ∉ op.getResults! ctx.raw) (rNotOp : rhs ∉ op.getResults! ctx.raw)
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) ipIn')
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpatternOrig hReturnVIB hReturnV hReturnCtx)
      (.at (.before op)) (.at (.before op)) ipIn ipIn')
    (hExtId : ext = none → ∀ r, e r = r)
    (hExtSem : ∀ eo, ext = some eo → ∀ (props : HasDialectOpInfo.propertiesOf eo.op)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (r : Data.RISCV.Reg),
        Riscv.interpretOp' eo.op props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (e r)], mem, none)))
    (hData : ∀ xt yt : Data.LLVM.Int bw, xVal ⊒ xt → yVal ⊒ yt →
      srcVal ⊒ RISCV.Reg.toInt
        (Data.RISCV.sltu (Data.RISCV.xor (e (LLVM.Int.toReg xt)) (e (LLVM.Int.toReg yt)))
          (Data.RISCV.li (BitVec.ofInt 64 0))) 1) :
    ∃ newState', interpretOpList newOps.toList state'
        (by grind [LocalRewritePattern.ReturnOps]) = some (newState', none) ∧
      newState.memory = newState'.memory ∧
      ∃ targetValues, newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
        (#[RuntimeValue.int 1 srcVal] : Array RuntimeValue) ⊒ targetValues := by
  simp only [icmpEmitXorSnezLocal, bind, Option.bind_eq_some_iff] at hEmit
  obtain ⟨⟨ctxP, pre, a, b⟩, hCE, hEmit⟩ := hEmit
  obtain ⟨⟨ctx₅, xorOp⟩, hXor, hEmit⟩ := hEmit
  replace hXor := WfRewriter.createOp!_none_some hXor
  obtain ⟨_, _, _, hXor⟩ := hXor
  obtain ⟨⟨ctx₆, liOp⟩, hLi, hEmit⟩ := hEmit
  replace hLi := WfRewriter.createOp!_none_some hLi
  obtain ⟨_, _, _, hLi⟩ := hLi
  obtain ⟨⟨ctx₇, cmpOp⟩, hCmp, hEmit⟩ := hEmit
  replace hCmp := WfRewriter.createOp!_none_some hCmp
  obtain ⟨_, _, _, hCmp⟩ := hCmp
  obtain ⟨⟨ctx₈, castBackOp⟩, hCastBack, hEmit⟩ := hEmit
  simp only [replaceWithRegLocal] at hCastBack
  replace hCastBack := WfRewriter.createOp!_none_some hCastBack
  obtain ⟨_, _, _, hCastBack⟩ := hCastBack
  obtain ⟨rfl, rfl, rfl⟩ := by simpa using hEmit
  -- Context extensions: prologue, then this arm's creations.
  have Ep := icmpCastExtLocal_extends opInBounds hCE
  have hOpInP : op.InBounds ctxP.raw := Ep.inBounds op opInBounds
  have E₅ := CtxExtends.of_createOp hXor hOpInP
  have E₆ := CtxExtends.of_createOp hLi (E₅.inBounds op hOpInP)
  have E₇ := CtxExtends.of_createOp hCmp (E₆.inBounds op (E₅.inBounds op hOpInP))
  have E₈ := CtxExtends.of_createOp hCastBack
    (E₇.inBounds op (E₆.inBounds op (E₅.inBounds op hOpInP)))
  have hExtP : CtxExtends op ctxP ctx₈ := E₅.trans (E₆.trans (E₇.trans E₈))
  have Ectx : CtxExtends op ctx ctx₈ := Ep.trans hExtP
  have hOpsIn : ∀ o ∈ (pre ++ #[xorOp, liOp, cmpOp, castBackOp]).toList, o.InBounds ctx₈.raw := by
    grind [LocalRewritePattern.ReturnOps]
  have hPreIn : ∀ o ∈ pre.toList, o.InBounds ctx₈.raw := by
    intro o ho
    exact hOpsIn o (by simp only [Array.toList_append, List.mem_append]; exact Or.inl ho)
  obtain ⟨xt, hLVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hLhsIn hxVal
      hDomCtxL (Ectx.dominates lhs hDomCtxL) lNotOp
  obtain ⟨yt, hRVal', hytRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hRhsIn hyVal
      hDomCtxR (Ectx.dominates rhs hDomCtxR) rNotOp
  obtain ⟨sPre, hPre, hPreMem, hAVal, hBVal⟩ :=
    icmpCastExtLocal_run opInBounds hCE hExtP hExtId hExtSem hRhsIn hLVal' hRVal' hPreIn
  have hXorIn₅ : xorOp.InBounds ctx₅.raw := WfRewriter.createOp_new_inBounds _ hXor
  have hLiIn₆ : liOp.InBounds ctx₆.raw := WfRewriter.createOp_new_inBounds _ hLi
  have hLiFresh₅ : ¬ liOp.InBounds ctx₅.raw := WfRewriter.createOp_new_not_inBounds _ hLi
  have hCmpIn₇ : cmpOp.InBounds ctx₇.raw := WfRewriter.createOp_new_inBounds _ hCmp
  have hXorResIn₅ : (ValuePtr.opResult (xorOp.getResult 0)).InBounds ctx₅.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hXorType : xorOp.getOpType! ctx₈.raw = .riscv .xor := by
    rw [(E₆.trans (E₇.trans E₈)).opType xorOp hXorIn₅]; grind
  have hXorOperands : xorOp.getOperands! ctx₈.raw = #[b, a] := by
    rw [(E₆.trans (E₇.trans E₈)).operands xorOp hXorIn₅]; grind
  have hXorResTypes : xorOp.getResultTypes! ctx₈.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [(E₆.trans (E₇.trans E₈)).resultTypes xorOp hXorIn₅]; grind
  have hLiType : liOp.getOpType! ctx₈.raw = .riscv .li := by
    rw [(E₇.trans E₈).opType liOp hLiIn₆]; grind
  have hLiOperands : liOp.getOperands! ctx₈.raw = #[] := by
    rw [(E₇.trans E₈).operands liOp hLiIn₆]; grind
  have hLiResTypes : liOp.getResultTypes! ctx₈.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [(E₇.trans E₈).resultTypes liOp hLiIn₆]; grind
  have hLiProps : liOp.getProperties! ctx₈.raw (.riscv .li) = icmpZeroImm := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hCmp (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hLi (operation := liOp)]
  have hCmpType : cmpOp.getOpType! ctx₈.raw = .riscv .sltu := by
    rw [E₈.opType cmpOp hCmpIn₇]; grind
  have hCmpOperands : cmpOp.getOperands! ctx₈.raw
      = #[ValuePtr.opResult (liOp.getResult 0), ValuePtr.opResult (xorOp.getResult 0)] := by
    rw [E₈.operands cmpOp hCmpIn₇]; grind
  have hCmpResTypes : cmpOp.getResultTypes! ctx₈.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    rw [E₈.resultTypes cmpOp hCmpIn₇]; grind
  have hCastBackType : castBackOp.getOpType! ctx₈.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₈.raw = #[ValuePtr.opResult (cmpOp.getResult 0)] := by grind
  have isT : Attribute.isType (Attribute.integerType (⟨1⟩ : IntegerType)) := by grind
  have hCBType : ((op.getResult 0).get! ctx₇.raw).type
      = (⟨Attribute.integerType ⟨1⟩, isT⟩ : TypeAttr) := by
    have h1 := (Ep.trans (E₅.trans (E₆.trans E₇))).valueType
      (ValuePtr.opResult (op.getResult 0)) hResIn
    simp only [ValuePtr.getType!_opResult] at h1
    apply Subtype.ext
    rw [show ((op.getResult 0).get! ctx₇.raw).type = ((op.getResult 0).get! ctx.raw).type from h1]
    exact hResType
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₈.raw
      = #[⟨Attribute.integerType ⟨1⟩, isT⟩] := by grind
  obtain ⟨s₅, hI₅, hMem₅, hRes₅, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := sPre) (inBounds := hOpsIn xorOp (by simp))
      (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁) (fun _ _ _ _ => rfl)
      hXorType hXorOperands hXorResTypes hBVal hAVal
  obtain ⟨s₆, hI₆, hMem₆, hRes₆, hFrame₆⟩ :=
    interpretOp_riscv_li_forward (state := s₅) (inBounds := hOpsIn liOp (by simp))
      (props := icmpZeroImm) hLiType hLiProps hLiOperands hLiResTypes
  have hXorRes₆ : s₆.variables.getVar? (ValuePtr.opResult (xorOp.getResult 0))
      = some (.reg (Data.RISCV.xor (e (LLVM.Int.toReg xt)) (e (LLVM.Int.toReg yt)))) := by
    rw [hFrame₆ _ (ValuePtr.not_mem_getResults!_of_inBounds_of_not_inBounds hXorResIn₅ hLiFresh₅)]
    exact hRes₅
  obtain ⟨s₇, hI₇, hMem₇, hRes₇, -⟩ :=
    interpretOp_riscv_binaryReg_forward (state := s₆) (inBounds := hOpsIn cmpOp (by simp))
      (f := fun r₁ r₂ => Data.RISCV.sltu r₂ r₁) (fun _ _ _ _ => rfl)
      hCmpType hCmpOperands hCmpResTypes hRes₆ hXorRes₆
  obtain ⟨s₈, hI₈, hMem₈, hRes₈, -⟩ :=
    interpretOp_castBack_forward (state := s₇) (inBounds := hOpsIn castBackOp (by simp))
      hCastBackType hCastBackOperands hCastBackResTypes hRes₇
  refine ⟨s₈, ?_, by grind, ?_⟩
  · simp only [Array.toList_append]
    rw [interpretOpList_append, hPre]
    simp [interpretOpList_cons, hI₅, hI₆, hI₇, hI₈, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.xor (e (LLVM.Int.toReg xt)) (e (LLVM.Int.toReg yt)))
        (Data.RISCV.li (BitVec.ofInt 64 icmpZeroImm.value.value))) 1)], ?_, ?_⟩
    · simp [hRes₈, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr
        ⟨rfl, by simpa [icmpZeroImm] using hData xt yt hxtRef hytRef⟩

/-! ### Data-level refinement lemmas

Each arm's data obligation has the shape `icmp x y pred ⊒ RISCV.Reg.toInt (…) 1`, where the source
operands `x`/`y` are replaced by refinements `xt`/`yt` (via `icmp_mono`) and each register holds the
sign-extension `e (toReg ·)` of its operand: `sextw` at `i32`, `sextb` at `i8`, and the identity at
`i64` (`toReg` already zero-extends into the full register).

Sign-extending both operands preserves *both* comparison orders: for the signed comparisons it is
required (`toReg` zero-extends, so a negative narrow operand would look positive), and it is
harmless for the unsigned ones because sign-extension is monotone for the unsigned order (it maps
the two halves of the narrow range to two intervals of the wide range in the same relative order).
-/

/-- `icmp eq` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_eq_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.eq ⊒
      RISCV.Reg.toInt (Data.RISCV.sltiu 1#12
        (Data.RISCV.xor (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x)))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp ne` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_ne_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ne ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.xor (Data.RISCV.sextw (LLVM.Int.toReg y)) (Data.RISCV.sextw (LLVM.Int.toReg x)))
        (Data.RISCV.li 0#64)) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp slt` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_slt_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.slt ⊒
      RISCV.Reg.toInt (Data.RISCV.slt (Data.RISCV.sextw (LLVM.Int.toReg y))
        (Data.RISCV.sextw (LLVM.Int.toReg x))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp sle` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_sle_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sle ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt (Data.RISCV.sextw (LLVM.Int.toReg x))
          (Data.RISCV.sextw (LLVM.Int.toReg y)))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp sgt` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_sgt_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sgt ⊒
      RISCV.Reg.toInt (Data.RISCV.slt (Data.RISCV.sextw (LLVM.Int.toReg x))
        (Data.RISCV.sextw (LLVM.Int.toReg y))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp sge` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_sge_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sge ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x)))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp ult` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_ult_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ult ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.sextw (LLVM.Int.toReg y))
        (Data.RISCV.sextw (LLVM.Int.toReg x))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp ule` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_ule_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ule ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu (Data.RISCV.sextw (LLVM.Int.toReg x))
          (Data.RISCV.sextw (LLVM.Int.toReg y)))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp ugt` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_ugt_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ugt ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.sextw (LLVM.Int.toReg x))
        (Data.RISCV.sextw (LLVM.Int.toReg y))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp uge` on `i32` operands, sign-extended into their registers. -/
theorem icmp_refinement_uge_32 {x y : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.uge ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu (Data.RISCV.sextw (LLVM.Int.toReg y))
          (Data.RISCV.sextw (LLVM.Int.toReg x)))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp eq x 0` on `i32`: the zero-compare peephole. -/
theorem icmp_refinement_eq_zero_rhs_32 {x : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 32 0) Data.LLVM.IntPred.eq ⊒
      RISCV.Reg.toInt (Data.RISCV.sltiu 1#12 (Data.RISCV.sextw (LLVM.Int.toReg x))) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp ne x 0` on `i32`: the zero-compare peephole. -/
theorem icmp_refinement_ne_zero_rhs_32 {x : Data.LLVM.Int 32} :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 32 0) Data.LLVM.IntPred.ne ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.sextw (LLVM.Int.toReg x))
        (Data.RISCV.li 0#64)) 1 := by
  simp only [Data.RISCV.sextw, Data.RISCV.addiw]
  veir_bv_decide

/-- `icmp eq` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_eq_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.eq ⊒
      RISCV.Reg.toInt (Data.RISCV.sltiu 1#12
        (Data.RISCV.xor (Data.RISCV.sextb (LLVM.Int.toReg y))
          (Data.RISCV.sextb (LLVM.Int.toReg x)))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp ne` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_ne_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ne ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu
        (Data.RISCV.xor (Data.RISCV.sextb (LLVM.Int.toReg y)) (Data.RISCV.sextb (LLVM.Int.toReg x)))
        (Data.RISCV.li 0#64)) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp slt` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_slt_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.slt ⊒
      RISCV.Reg.toInt (Data.RISCV.slt (Data.RISCV.sextb (LLVM.Int.toReg y))
        (Data.RISCV.sextb (LLVM.Int.toReg x))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp sle` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_sle_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sle ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt (Data.RISCV.sextb (LLVM.Int.toReg x))
          (Data.RISCV.sextb (LLVM.Int.toReg y)))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp sgt` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_sgt_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sgt ⊒
      RISCV.Reg.toInt (Data.RISCV.slt (Data.RISCV.sextb (LLVM.Int.toReg x))
        (Data.RISCV.sextb (LLVM.Int.toReg y))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp sge` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_sge_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sge ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.slt (Data.RISCV.sextb (LLVM.Int.toReg y))
          (Data.RISCV.sextb (LLVM.Int.toReg x)))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp ult` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_ult_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ult ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.sextb (LLVM.Int.toReg y))
        (Data.RISCV.sextb (LLVM.Int.toReg x))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp ule` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_ule_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ule ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu (Data.RISCV.sextb (LLVM.Int.toReg x))
          (Data.RISCV.sextb (LLVM.Int.toReg y)))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp ugt` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_ugt_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ugt ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.sextb (LLVM.Int.toReg x))
        (Data.RISCV.sextb (LLVM.Int.toReg y))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp uge` on `i8` operands, sign-extended into their registers. -/
theorem icmp_refinement_uge_8 {x y : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x y Data.LLVM.IntPred.uge ⊒
      RISCV.Reg.toInt (Data.RISCV.xori 1#12
        (Data.RISCV.sltu (Data.RISCV.sextb (LLVM.Int.toReg y))
          (Data.RISCV.sextb (LLVM.Int.toReg x)))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp eq x 0` on `i8`: the zero-compare peephole. -/
theorem icmp_refinement_eq_zero_rhs_8 {x : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 8 0) Data.LLVM.IntPred.eq ⊒
      RISCV.Reg.toInt (Data.RISCV.sltiu 1#12 (Data.RISCV.sextb (LLVM.Int.toReg x))) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-- `icmp ne x 0` on `i8`: the zero-compare peephole. -/
theorem icmp_refinement_ne_zero_rhs_8 {x : Data.LLVM.Int 8} :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 8 0) Data.LLVM.IntPred.ne ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu (Data.RISCV.sextb (LLVM.Int.toReg x))
        (Data.RISCV.li 0#64)) 1 := by
  simp only [Data.RISCV.sextb]
  veir_bv_decide

/-! ### Bundling the data facts per width

The twelve arms of `icmp_local` need twelve data-level refinements, all at the source operands'
width and all mentioning the same extension `e`. `icmpData_of_bitwidth` produces, for each legal
width, the extension semantics together with all twelve, so the dispatch below can quote them
uniformly. -/

/-- The data-level refinements the `icmp` arms need at operand width `bw`, when each operand
    register holds `e` of the operand. `eqZero`/`neZero` are the zero-compare peepholes. -/
structure IcmpData (bw : Nat) (e : Data.RISCV.Reg → Data.RISCV.Reg) : Prop where
  slt : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.slt ⊒
    RISCV.Reg.toInt (Data.RISCV.slt (e (LLVM.Int.toReg y)) (e (LLVM.Int.toReg x))) 1
  sgt : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sgt ⊒
    RISCV.Reg.toInt (Data.RISCV.slt (e (LLVM.Int.toReg x)) (e (LLVM.Int.toReg y))) 1
  ult : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ult ⊒
    RISCV.Reg.toInt (Data.RISCV.sltu (e (LLVM.Int.toReg y)) (e (LLVM.Int.toReg x))) 1
  ugt : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ugt ⊒
    RISCV.Reg.toInt (Data.RISCV.sltu (e (LLVM.Int.toReg x)) (e (LLVM.Int.toReg y))) 1
  sge : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sge ⊒
    RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 1)
      (Data.RISCV.slt (e (LLVM.Int.toReg y)) (e (LLVM.Int.toReg x)))) 1
  sle : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.sle ⊒
    RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 1)
      (Data.RISCV.slt (e (LLVM.Int.toReg x)) (e (LLVM.Int.toReg y)))) 1
  uge : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.uge ⊒
    RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 1)
      (Data.RISCV.sltu (e (LLVM.Int.toReg y)) (e (LLVM.Int.toReg x)))) 1
  ule : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ule ⊒
    RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 1)
      (Data.RISCV.sltu (e (LLVM.Int.toReg x)) (e (LLVM.Int.toReg y)))) 1
  eq : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.eq ⊒
    RISCV.Reg.toInt (Data.RISCV.sltiu (BitVec.ofInt 12 1)
      (Data.RISCV.xor (e (LLVM.Int.toReg x)) (e (LLVM.Int.toReg y)))) 1
  ne : ∀ x y : Data.LLVM.Int bw, Data.LLVM.Int.icmp x y Data.LLVM.IntPred.ne ⊒
    RISCV.Reg.toInt (Data.RISCV.sltu
      (Data.RISCV.xor (e (LLVM.Int.toReg x)) (e (LLVM.Int.toReg y)))
      (Data.RISCV.li (BitVec.ofInt 64 0))) 1
  eqZero : ∀ x : Data.LLVM.Int bw,
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant bw 0) Data.LLVM.IntPred.eq ⊒
      RISCV.Reg.toInt (Data.RISCV.sltiu (BitVec.ofInt 12 1) (e (LLVM.Int.toReg x))) 1
  neZero : ∀ x : Data.LLVM.Int bw,
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant bw 0) Data.LLVM.IntPred.ne ⊒
      RISCV.Reg.toInt (Data.RISCV.sltu (e (LLVM.Int.toReg x)) (Data.RISCV.li (BitVec.ofInt 64 0))) 1

/-- `riscv.xor` is commutative; the `eq`/`ne` arms feed it its operands in the opposite order from
    the one the data lemmas are stated in. -/
private theorem riscv_xor_comm (r₁ r₂ : Data.RISCV.Reg) :
    Data.RISCV.xor r₁ r₂ = Data.RISCV.xor r₂ r₁ := by
  simp only [Data.RISCV.xor, BitVec.xor_comm]

/-- At each legal operand width, the sign-extension chosen by `icmpExtOf` has semantics `e`, and all
    twelve data-level refinements hold for it. -/
theorem icmpData_of_bitwidth {bw : Nat} (hBw : bw = 64 ∨ bw = 32 ∨ bw = 8) :
    ∃ e : Data.RISCV.Reg → Data.RISCV.Reg,
      (icmpExtOf bw = none → ∀ r, e r = r) ∧
      (∀ eo, icmpExtOf bw = some eo → ∀ (props : HasDialectOpInfo.propertiesOf eo.op)
        (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr) (mem : MemoryState)
        (r : Data.RISCV.Reg),
        Riscv.interpretOp' eo.op props resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (e r)], mem, none))) ∧
      IcmpData bw e := by
  rcases hBw with rfl | rfl | rfl
  · refine ⟨id, fun _ _ => rfl, by simp [icmpExtOf], ?_⟩
    exact ⟨fun x y => by simpa using Data.RISCV.icmp_refinement_slt (x := x) (y := y),
      fun x y => by simpa using Data.RISCV.icmp_refinement_sgt (x := x) (y := y),
      fun x y => by simpa using Data.RISCV.icmp_refinement_ult (x := x) (y := y),
      fun x y => by simpa using Data.RISCV.icmp_refinement_ugt (x := x) (y := y),
      fun x y => by simpa using Data.RISCV.icmp_refinement_sge (x := x) (y := y),
      fun x y => by simpa using Data.RISCV.icmp_refinement_sle (x := x) (y := y),
      fun x y => by simpa using Data.RISCV.icmp_refinement_uge (x := x) (y := y),
      fun x y => by simpa using Data.RISCV.icmp_refinement_ule (x := x) (y := y),
      fun x y => by rw [riscv_xor_comm]; simpa using Data.RISCV.icmp_refinement_eq (x := x) (y := y),
      fun x y => by rw [riscv_xor_comm]; simpa using Data.RISCV.icmp_refinement_ne (x := x) (y := y),
      fun x => by simpa using Data.RISCV.icmp_refinement_eq_zero_rhs (x := x),
      fun x => by simpa using Data.RISCV.icmp_refinement_ne_zero_rhs (x := x)⟩
  · refine ⟨Data.RISCV.sextw, by simp [icmpExtOf], ?_, ?_⟩
    · rintro eo heq
      obtain rfl : eo = ⟨.sextw, rfl⟩ := by simpa [icmpExtOf] using heq.symm
      intro props rt bo mem r
      rfl
    · exact ⟨fun x y => icmp_refinement_slt_32, fun x y => icmp_refinement_sgt_32,
        fun x y => icmp_refinement_ult_32, fun x y => icmp_refinement_ugt_32,
        fun x y => icmp_refinement_sge_32, fun x y => icmp_refinement_sle_32,
        fun x y => icmp_refinement_uge_32, fun x y => icmp_refinement_ule_32,
        fun x y => by rw [riscv_xor_comm]; exact icmp_refinement_eq_32,
        fun x y => by rw [riscv_xor_comm]; exact icmp_refinement_ne_32,
        fun x => icmp_refinement_eq_zero_rhs_32, fun x => icmp_refinement_ne_zero_rhs_32⟩
  · refine ⟨Data.RISCV.sextb, by simp [icmpExtOf], ?_, ?_⟩
    · rintro eo heq
      obtain rfl : eo = ⟨.sextb, rfl⟩ := by simpa [icmpExtOf] using heq.symm
      intro props rt bo mem r
      rfl
    · exact ⟨fun x y => icmp_refinement_slt_8, fun x y => icmp_refinement_sgt_8,
        fun x y => icmp_refinement_ult_8, fun x y => icmp_refinement_ugt_8,
        fun x y => icmp_refinement_sge_8, fun x y => icmp_refinement_sle_8,
        fun x y => icmp_refinement_uge_8, fun x y => icmp_refinement_ule_8,
        fun x y => by rw [riscv_xor_comm]; exact icmp_refinement_eq_8,
        fun x y => by rw [riscv_xor_comm]; exact icmp_refinement_ne_8,
        fun x => icmp_refinement_eq_zero_rhs_8, fun x => icmp_refinement_ne_zero_rhs_8⟩

/-! ### Correctness of `icmp_local` -/

set_option maxHeartbeats 1600000 in
theorem icmp_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps icmp_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges icmp_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds icmp_local}
    {h₄ : LocalRewritePattern.ReturnValues icmp_local} :
    LocalRewritePattern.PreservesSemantics icmp_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  -- `hEmitPat` is unfolded so the matcher and the guards can be peeled; `hpattern` stays in
  -- `icmp_local ctx op = …` form for the `mapping` in `valueRefinement`.
  have hEmitPat := hpattern
  simp only [icmp_local] at hEmitPat
  simp [pure] at hEmitPat
  -- Peel the matcher.
  have hMatchSome : (matchIcmp op ctx.raw).isSome := by
    cases hM : matchIcmp op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hEmitPat; simp at hEmitPat
  obtain ⟨⟨lhs, rhs, prop⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hEmitPat
  simp only [] at hEmitPat
  have ⟨hOpType, hNumResults, hOperands, hProps⟩ := matchIcmp_implies hMatch
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, ⟨i1ty, hResTypeV, hResBw⟩, hOpEqType⟩ :=
    OperationPtr.Verified.llvm_icmp opVerif hOpType
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  rw [hOperand0, hOperand1] at hOpEqType
  -- Peel the `.integerType` match on the operands' type and the two bitwidth guards.
  have hLhsTySome : ∃ lt, (lhs.getType! ctx.raw).val = Attribute.integerType lt := by
    cases hlt : (lhs.getType! ctx.raw).val with
    | integerType lt => exact ⟨lt, rfl⟩
    | _ => rw [hlt] at hEmitPat; simp at hEmitPat
  obtain ⟨lt, hLhsType⟩ := hLhsTySome
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType lt := by
    rw [← hOpEqType, hLhsType]
  simp only [hLhsType] at hEmitPat
  peelSplittableCondition [hBw] hEmitPat
  simp only [hRhsType] at hEmitPat
  peelSplittableCondition [hBwR] hEmitPat
  -- Peel the `.integerType` match on the result type.
  simp only [hResTypeV] at hEmitPat
  -- Unfold the interpretation of the source `icmp`: exposes both operand values.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchIcmp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hinterp
      hLhsType hRhsType
  subst hCf
  have hDomCtxL : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have hDomCtxR : rhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `icmp x y pred`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have lNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  have rNotOp : ¬ rhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  obtain ⟨bw⟩ := lt
  obtain ⟨w⟩ := i1ty
  simp only at hResBw
  subst hResBw
  have hResType1 : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩ := hResTypeV
  have hResIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    grind [ValuePtr.InBounds, OpResultPtr.InBounds, OperationPtr.getResult]
  have hLhsIn : lhs.InBounds ctx.raw := by rw [← hOperand0]; grind
  have hRhsIn : rhs.InBounds ctx.raw := by rw [← hOperand1]; grind
  -- The extension semantics and the twelve data-level refinements at this width.
  obtain ⟨e, hExtId, hExtSem, hD⟩ := icmpData_of_bitwidth (bw := bw) (by grind)
  -- The `eq`/`ne` peephole guard: pin the rhs to the constant `0` when it fires.
  have hZero : (matchConstantZero rhs ctx).isSome = true → yVal = Data.LLVM.Int.constant bw 0 := by
    intro hIsSome
    obtain ⟨_, hCZ⟩ := Option.isSome_iff_exists.mp hIsSome
    obtain ⟨-, attr, hCstVal, hAttrZero⟩ := matchConstantZero_implies hCZ
    have hyConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
      stateWf hCstVal (by rw [hOperands]; simp) hRhsType
    rw [hAttrZero] at hyConst
    have := hyVal.symm.trans hyConst
    simpa using this
  -- Dispatch on the predicate; every arm delegates to its `icmpEmit*Local_sound` lemma.
  split at hEmitPat
  · -- eq
    rw [show prop.predicate = Data.LLVM.IntPred.eq from by assumption] at hRes ⊢
    split at hEmitPat
    · rename_i hIsZero
      obtain rfl := hZero hIsZero
      exact icmpEmitSeqzLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
        hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
        hExtId hExtSem
        (fun xt hxt => isRefinedBy_trans (Data.LLVM.Int.icmp_mono _ _ xt _ _ hxt
          (isRefinedBy_refl _)) (hD.eqZero xt))
        (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
    · exact icmpEmitCmpImmLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
        hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
        hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.xor r₂ r₁)
        (g := fun r => Data.RISCV.sltiu (BitVec.ofInt 12 1) r) (fun _ _ _ _ _ _ => rfl)
        (fun _ _ _ _ => rfl)
        (fun xt yt hxt hyt => isRefinedBy_trans
          (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.eq xt yt))
        (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- ne
    rw [show prop.predicate = Data.LLVM.IntPred.ne from by assumption] at hRes ⊢
    split at hEmitPat
    · rename_i hIsZero
      obtain rfl := hZero hIsZero
      exact icmpEmitSnezLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
        hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
        hExtId hExtSem
        (fun xt hxt => isRefinedBy_trans (Data.LLVM.Int.icmp_mono _ _ xt _ _ hxt
          (isRefinedBy_refl _)) (hD.neZero xt))
        (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
    · exact icmpEmitXorSnezLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
        hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
        hExtId hExtSem
        (fun xt yt hxt hyt => isRefinedBy_trans
          (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (hD.ne xt yt))
        (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- slt
    rw [show prop.predicate = Data.LLVM.IntPred.slt from by assumption] at hRes ⊢
    exact icmpEmitCmpLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.slt r₂ r₁) (fun _ _ _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.slt xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- sgt
    rw [show prop.predicate = Data.LLVM.IntPred.sgt from by assumption] at hRes ⊢
    exact icmpEmitCmpLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.slt r₂ r₁) (fun _ _ _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.sgt xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- ult
    rw [show prop.predicate = Data.LLVM.IntPred.ult from by assumption] at hRes ⊢
    exact icmpEmitCmpLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.sltu r₂ r₁) (fun _ _ _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.ult xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- ugt
    rw [show prop.predicate = Data.LLVM.IntPred.ugt from by assumption] at hRes ⊢
    exact icmpEmitCmpLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.sltu r₂ r₁) (fun _ _ _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.ugt xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- sge
    rw [show prop.predicate = Data.LLVM.IntPred.sge from by assumption] at hRes ⊢
    exact icmpEmitCmpImmLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.slt r₂ r₁)
      (g := fun r => Data.RISCV.xori (BitVec.ofInt 12 1) r) (fun _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.sge xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- sle
    rw [show prop.predicate = Data.LLVM.IntPred.sle from by assumption] at hRes ⊢
    exact icmpEmitCmpImmLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.slt r₂ r₁)
      (g := fun r => Data.RISCV.xori (BitVec.ofInt 12 1) r) (fun _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.sle xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- uge
    rw [show prop.predicate = Data.LLVM.IntPred.uge from by assumption] at hRes ⊢
    exact icmpEmitCmpImmLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.sltu r₂ r₁)
      (g := fun r => Data.RISCV.xori (BitVec.ofInt 12 1) r) (fun _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.uge xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)
  · -- ule
    rw [show prop.predicate = Data.LLVM.IntPred.ule from by assumption] at hRes ⊢
    exact icmpEmitCmpImmLocal_sound opInBounds hpattern hEmitPat hResType1 hResIn hLhsIn hRhsIn
      hxVal hyVal hMem memoryRefinement hDomCtxL hDomCtxR lNotOp rNotOp state'Dom valueRefinement
      hExtId hExtSem (f := fun r₁ r₂ => Data.RISCV.sltu r₂ r₁)
      (g := fun r => Data.RISCV.xori (BitVec.ofInt 12 1) r) (fun _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ => rfl)
      (fun xt yt hxt hyt => isRefinedBy_trans
        (Data.LLVM.Int.icmp_mono _ _ xt yt _ hxt hyt) (by simpa using hD.ule xt yt))
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄)

end Veir
