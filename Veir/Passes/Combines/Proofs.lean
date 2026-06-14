import Veir.Data.RISCV.Reg.Basic
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.Combines.Combine
import Veir.PatternRewriter.Semantics

/-!
  In this file we prove the correctness of the RISCV combines.
-/

namespace Veir

/-! ## Purity of the relevant RISC-V opcodes

  `EquationLemmaAt` (the SSA invariant) is stated over `OperationPtr.Pure`, so to read the
  value an operand was defined with we must know its defining op is pure. These opcodes all
  thread the memory through unchanged, hence are pure. -/

/--
  Reduce `op.Pure ctx` to a memory-purity fact about the single opcode `op` carries.
  The `generalize`/`subst` discharges the dependent rewrite of `op.getOpType! ctx` inside
  `op.getProperties! ctx (op.getOpType! ctx)`.
-/
theorem Pure_of_getOpType_riscv {op : OperationPtr} {ctx : IRContext OpCode} {rop : Riscv}
    (h : op.getOpType! ctx = OpCode.riscv rop)
    (hpure : ∀ (props : HasOpInfo.propertiesOf (OpCode.riscv rop)) (rt : Array TypeAttr)
        (operands : Array RuntimeValue) (succ : Array BlockPtr) (m₁ m₂ : MemoryState),
      interpretOp' (OpCode.riscv rop) props rt operands succ m₁
        = (interpretOp' (OpCode.riscv rop) props rt operands succ m₂).map
            (fun (r, _, cf) => (r, m₁, cf))) :
    op.Pure ctx := by
  intro operands m₁ m₂
  generalize hot : op.getOpType! ctx = ot at h ⊢
  subst h
  exact hpure _ _ _ _ _ _

theorem li_interpretOp'_mem_pure
    (props : HasOpInfo.propertiesOf (OpCode.riscv .li)) (rt : Array TypeAttr)
    (operands : Array RuntimeValue) (succ : Array BlockPtr) (m₁ m₂ : MemoryState) :
    interpretOp' (OpCode.riscv .li) props rt operands succ m₁
      = (interpretOp' (OpCode.riscv .li) props rt operands succ m₂).map
          (fun (r, _, cf) => (r, m₁, cf)) := by
  simp only [interpretOp', Riscv.interpretOp', Interp.map, Option.map, UBOr.map, pure]

theorem zextw_interpretOp'_mem_pure
    (props : HasOpInfo.propertiesOf (OpCode.riscv .zextw)) (rt : Array TypeAttr)
    (operands : Array RuntimeValue) (succ : Array BlockPtr) (m₁ m₂ : MemoryState) :
    interpretOp' (OpCode.riscv .zextw) props rt operands succ m₁
      = (interpretOp' (OpCode.riscv .zextw) props rt operands succ m₂).map
          (fun (r, _, cf) => (r, m₁, cf)) := by
  simp only [interpretOp', Riscv.interpretOp', Interp.map, Option.map, UBOr.map, pure]
  split <;> rfl

/-- A `riscv.li` operation is pure. -/
theorem Pure_of_getOpType_li {op : OperationPtr} {ctx : IRContext OpCode}
    (h : op.getOpType! ctx = OpCode.riscv .li) : op.Pure ctx :=
  Pure_of_getOpType_riscv h li_interpretOp'_mem_pure

/-- A `riscv.zextw` operation is pure. -/
theorem Pure_of_getOpType_zextw {op : OperationPtr} {ctx : IRContext OpCode}
    (h : op.getOpType! ctx = OpCode.riscv .zextw) : op.Pure ctx :=
  Pure_of_getOpType_riscv h zextw_interpretOp'_mem_pure

/-! ## Reading a matched `li`'s value from the SSA equation lemma (toward PreservesSemantics)

  These are the next bricks: a successful `matchLi` is a `getDefiningOp!` + `matchOp`, and a
  `riscv.li` op evaluates to its loaded constant under any operands/memory. Together with the
  purity above and the SSA dominance axioms, they let us read the value an `li`-defined operand
  holds in a state satisfying `EquationLemmaAt`. -/

/-- Decompose a successful `matchLi`: it found a defining op that `matchOp` accepts as `riscv.li`. -/
theorem matchLi_some {rhs : ValuePtr} {ctx : IRContext OpCode}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .li)}
    (h : RISCV.matchLi rhs ctx = some imm) :
    ∃ liOp ops, rhs.getDefiningOp! ctx = some liOp ∧
      matchOp liOp ctx (OpCode.riscv .li) 0 = some (ops, imm) := by
  unfold RISCV.matchLi at h
  obtain ⟨liOp, hdef, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨ops, props⟩, hmatch, hres⟩ := Option.bind_eq_some_iff.mp h
  have : props = imm := Option.some.inj hres
  subst this
  exact ⟨liOp, ops, hdef, hmatch⟩

/-- A `riscv.li` op evaluates to its loaded 64-bit constant, regardless of operands and memory. -/
theorem li_interpret_eq {liOp : OperationPtr} {ctx : IRContext OpCode}
    {operands : Array RuntimeValue} {mem : MemoryState}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .li)}
    (hty : liOp.getOpType! ctx = OpCode.riscv .li)
    (hprops : liOp.getProperties! ctx (OpCode.riscv .li) = imm) :
    liOp.interpret ctx operands mem
      = some (.ok (#[.reg (Data.RISCV.li (BitVec.ofInt 64 imm.value.value))], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : liOp.getOpType! ctx = ot at hty ⊢
  subst hty
  subst hprops
  simp only [interpretOp', Riscv.interpretOp', pure]

/--
  The payoff: in a state satisfying the SSA equation lemma before `op`, an operand of `op`
  that `matchLi` recognizes as a `riscv.li` holds exactly the loaded constant. This is the
  fact `PreservesSemantics` needs to pin down the source `sllw`'s immediate operand.

  Proof outline: the `li` op defines `rhs`, so (SSA dominance axiom) it strictly dominates
  `op`; it is pure; hence `EquationLemmaAt` says its result is already recorded in the state.
  Decomposing that recorded interpretation (`interpretOp_some_iff` + `li_interpret_eq`) and
  reading back the result (`getVar?_setResultValues?`) yields the constant.
-/
theorem getVar_li_of_equationLemma
    {ctx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {state : InterpreterState ctx} {op : OperationPtr} {rhs : ValuePtr}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .li)}
    (hopIn : op.InBounds ctx.raw)
    (hEq : state.EquationLemmaAt (.before op))
    (hmem : rhs ∈ op.getOperands! ctx.raw)
    (hmatch : RISCV.matchLi rhs ctx = some imm) :
    state.variables.getVar? rhs
      = some (.reg (Data.RISCV.li (BitVec.ofInt 64 imm.value.value))) := by
  obtain ⟨liOp, ops, hdef, hmatchOp⟩ := matchLi_some hmatch
  have hty : liOp.getOpType! ctx.raw = OpCode.riscv .li := (matchOp_eq hmatchOp).1
  have hprops : liOp.getProperties! ctx.raw (OpCode.riscv .li) = imm :=
    (matchOp_eq hmatchOp).2.2.2.2.symm
  have hrhsIn : rhs.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds hopIn hmem
  have hliopIn : liOp.InBounds ctx.raw := by
    have h := ValuePtr.getDefiningOp!_inBounds ctx.wellFormed.inBounds hrhsIn
    rw [hdef] at h; simpa [Option.maybe] using h
  have hdomIp : liOp.dominatesIp (.before op) ctx :=
    OperationPtr.dominatesIp_before.mpr
      (OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hdef hmem)
  obtain ⟨cf, hinterp⟩ := hEq liOp hliopIn (Pure_of_getOpType_li hty) hdomIp
  obtain ⟨operandValues, resValues, mem', varState', hov, hinterp', hset, hstate⟩ :=
    interpretOp_some_iff.mp hinterp
  rw [li_interpret_eq hty hprops] at hinterp'
  obtain ⟨opRes, hrhseq, howner⟩ := ValuePtr.getDefiningOp!_eq_some_iff.mp hdef
  have hopResIn : (ValuePtr.opResult opRes).InBounds ctx.raw := hrhseq ▸ hrhsIn
  have hriIn : opRes.InBounds ctx.raw := (ValuePtr.inBounds_opResult opRes ctx.raw).mp hopResIn
  obtain ⟨hh, hidx⟩ := OpResultPtr.inBounds_def.mp hriIn
  have hopeq : opRes.op = liOp := by
    have hro := (ctx.wellFormed.operations opRes.op hh).result_owner opRes.index (by grind)
    have heq := OperationPtr.eq_getResult_of_OpResultPtr_op_eq (op := opRes.op) (res := opRes) rfl
    grind
  have hgv := VariableState.getVar?_setResultValues?_of_value_inBounds hrhsIn hset (value := rhs)
  grind

/-- A `riscv.sllw rs2 rs1` evaluates to `RISCV.sllw rs2 rs1` (memory unchanged). -/
theorem sllw_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode}
    {o1 o2 : Data.RISCV.Reg} {mem : MemoryState}
    (hty : op.getOpType! ctx = OpCode.riscv .sllw) :
    op.interpret ctx #[.reg o1, .reg o2] mem
      = some (.ok (#[.reg (Data.RISCV.sllw o2 o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty
  simp only [interpretOp', Riscv.interpretOp', pure]

/-- A `riscv.slliw rs1` evaluates to `RISCV.slliw (ofInt 5 imm) rs1` (memory unchanged). -/
theorem slliw_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode}
    {o1 : Data.RISCV.Reg} {mem : MemoryState}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .slliw)}
    (hty : op.getOpType! ctx = OpCode.riscv .slliw)
    (hprops : op.getProperties! ctx (OpCode.riscv .slliw) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.slliw (BitVec.ofInt 5 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty
  subst hprops
  simp only [interpretOp', Riscv.interpretOp', pure]

/-- Inverting a successful `sllw` interpretation: its operands were two registers and its
    result is `RISCV.sllw` of them (with memory unchanged). -/
theorem sllw_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode}
    {ov : Array RuntimeValue} {mem : MemoryState} {res}
    (hty : op.getOpType! ctx = OpCode.riscv .sllw)
    (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.sllw o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty
  simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist
    exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

/-- The other imm5 source/destination interpreter facts (same shape as the `sllw`/`slliw` ones). -/
theorem srlw_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue}
    {mem res} (hty : op.getOpType! ctx = OpCode.riscv .srlw) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.srlw o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem sraw_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue}
    {mem res} (hty : op.getOpType! ctx = OpCode.riscv .sraw) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.sraw o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem rorw_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue}
    {mem res} (hty : op.getOpType! ctx = OpCode.riscv .rorw) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.rorw o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem srliw_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .srliw)}
    (hty : op.getOpType! ctx = OpCode.riscv .srliw)
    (hprops : op.getProperties! ctx (OpCode.riscv .srliw) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.srliw (BitVec.ofInt 5 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem sraiw_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .sraiw)}
    (hty : op.getOpType! ctx = OpCode.riscv .sraiw)
    (hprops : op.getProperties! ctx (OpCode.riscv .sraiw) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.sraiw (BitVec.ofInt 5 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem roriw_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .roriw)}
    (hty : op.getOpType! ctx = OpCode.riscv .roriw)
    (hprops : op.getProperties! ctx (OpCode.riscv .roriw) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.roriw (BitVec.ofInt 5 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

/-! ## imm6 interpreter facts (same shape as imm5, width-6 immediate). -/

theorem sll_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .sll) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.sll o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem srl_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .srl) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.srl o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem sra_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .sra) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.sra o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem ror_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .ror) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.ror o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem bclr_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .bclr) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.bclr o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem bext_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .bext) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.bext o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem binv_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .binv) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.binv o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem bset_interpret_inv {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res}
    (hty : op.getOpType! ctx = OpCode.riscv .bset) (h : op.interpret ctx ov mem = some res) :
    ∃ o1 o2 : Data.RISCV.Reg, ov = #[.reg o1, .reg o2] ∧
      res = .ok (#[.reg (Data.RISCV.bset o2 o1)], mem, none) := by
  unfold OperationPtr.interpret at h
  generalize hot : op.getOpType! ctx = ot at hty h
  subst hty; simp only [interpretOp', Riscv.interpretOp', pure] at h
  split at h
  · rename_i o1 o2 hlist; exact ⟨o1, o2, by grind [Array.toList_inj], by grind⟩
  · simp at h

theorem slli_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .slli)}
    (hty : op.getOpType! ctx = OpCode.riscv .slli) (hprops : op.getProperties! ctx (OpCode.riscv .slli) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.slli (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem srli_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .srli)}
    (hty : op.getOpType! ctx = OpCode.riscv .srli) (hprops : op.getProperties! ctx (OpCode.riscv .srli) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.srli (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem srai_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .srai)}
    (hty : op.getOpType! ctx = OpCode.riscv .srai) (hprops : op.getProperties! ctx (OpCode.riscv .srai) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.srai (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem rori_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .rori)}
    (hty : op.getOpType! ctx = OpCode.riscv .rori) (hprops : op.getProperties! ctx (OpCode.riscv .rori) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.rori (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem bclri_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .bclri)}
    (hty : op.getOpType! ctx = OpCode.riscv .bclri) (hprops : op.getProperties! ctx (OpCode.riscv .bclri) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.bclri (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem bexti_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .bexti)}
    (hty : op.getOpType! ctx = OpCode.riscv .bexti) (hprops : op.getProperties! ctx (OpCode.riscv .bexti) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.bexti (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem binvi_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .binvi)}
    (hty : op.getOpType! ctx = OpCode.riscv .binvi) (hprops : op.getProperties! ctx (OpCode.riscv .binvi) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.binvi (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]

theorem bseti_interpret_eq {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Data.RISCV.Reg} {mem}
    {imm : HasOpInfo.propertiesOf (OpCode.riscv .bseti)}
    (hty : op.getOpType! ctx = OpCode.riscv .bseti) (hprops : op.getProperties! ctx (OpCode.riscv .bseti) = imm) :
    op.interpret ctx #[.reg o1] mem
      = some (.ok (#[.reg (Data.RISCV.bseti (BitVec.ofInt 6 imm.value.value) o1)], mem, none)) := by
  unfold OperationPtr.interpret
  generalize hot : op.getOpType! ctx = ot at hty ⊢
  subst hty; subst hprops; simp only [interpretOp', Riscv.interpretOp', pure]


/-! ## Reading operand values out of `getOperandValues` -/

theorem getOperandValues_pair {ctx : WfIRContext OpCode} {state : VariableState ctx}
    {op : OperationPtr} {a b : ValuePtr} {va vb : RuntimeValue}
    (hops : op.getOperands! ctx.raw = #[a, b])
    (ha : state.getVar? a = some va) (hb : state.getVar? b = some vb) :
    state.getOperandValues op = some #[va, vb] := by
  simp [VariableState.getOperandValues, hops, Array.mapM_eq_mapM_toList, ha, hb]

theorem getOperandValues_single {ctx : WfIRContext OpCode} {state : VariableState ctx}
    {op : OperationPtr} {a : ValuePtr} {va : RuntimeValue}
    (hops : op.getOperands! ctx.raw = #[a]) (ha : state.getVar? a = some va) :
    state.getOperandValues op = some #[va] := by
  simp [VariableState.getOperandValues, hops, Array.mapM_eq_mapM_toList, ha]

theorem getOperandValues_pair_inv {ctx : WfIRContext OpCode} {state : VariableState ctx}
    {op : OperationPtr} {a b : ValuePtr} {ov : Array RuntimeValue}
    (hops : op.getOperands! ctx.raw = #[a, b])
    (h : state.getOperandValues op = some ov) :
    ∃ va vb, state.getVar? a = some va ∧ state.getVar? b = some vb ∧ ov = #[va, vb] := by
  have hane : state.getVar? a ≠ none := by
    intro hn; simp [VariableState.getOperandValues, hops, Array.mapM_eq_mapM_toList, hn] at h
  have hbne : state.getVar? b ≠ none := by
    intro hn; simp [VariableState.getOperandValues, hops, Array.mapM_eq_mapM_toList, hn] at h
  obtain ⟨va, ha⟩ := Option.ne_none_iff_exists'.mp hane
  obtain ⟨vb, hb⟩ := Option.ne_none_iff_exists'.mp hbne
  have hfwd := getOperandValues_pair hops ha hb
  rw [hfwd] at h
  exact ⟨va, vb, ha, hb, (Option.some.inj h).symm⟩

/-- The operands of an op matched by `matchRiscvBinop` are exactly `#[reg, rhs]`. -/
theorem matchRiscvBinop_getOperands {oc : Riscv} {op : OperationPtr} {ctx : IRContext OpCode}
    {reg rhs : ValuePtr} (h : RISCV.matchRiscvBinop oc op ctx = some (reg, rhs)) :
    op.getOpType! ctx = OpCode.riscv oc ∧ op.getOperands! ctx = #[reg, rhs] := by
  unfold RISCV.matchRiscvBinop at h
  obtain ⟨⟨ops, props⟩, hmatchOp, hres⟩ := Option.bind_eq_some_iff.mp h
  have hty := (matchOp_eq hmatchOp).1
  have hnum := matchOp_getNumOperands hmatchOp
  have hops := matchOp_operands hmatchOp
  have hreg : reg = ops[0]! := (congrArg Prod.fst (Option.some.inj hres)).symm
  have hrhs : rhs = ops[1]! := (congrArg Prod.snd (Option.some.inj hres)).symm
  have hsize : ops.size = 2 := by
    rw [hops, OperationPtr.getOperands!.size_eq_getNumOperands!]; exact hnum
  refine ⟨hty, ?_⟩
  rw [← hops, hreg, hrhs]
  apply Array.ext
  · simp [hsize]
  · intro i hi _
    match i, hi with
    | 0, _ => grind
    | 1, _ => grind
    | n+2, h => rw [hsize] at h; omega

/-- A one-result op's result list is the singleton `#[op.getResult 0]`. -/
theorem getResults!_single {op : OperationPtr} {ctx : IRContext OpCode}
    (h : op.getNumResults! ctx = 1) : op.getResults! ctx = #[(op.getResult 0 : ValuePtr)] := by
  unfold OperationPtr.getResults!
  rw [h, show Array.range 1 = #[0] by decide]
  simp

/-- The rewrite's value `mapping` is the identity on the matched op's operands (they are not
    among its results, by SSA dominance). -/
theorem mapping_operand {ctx newCtx : WfIRContext OpCode} (ctxDom : ctx.Dom)
    {pattern : LocalRewritePattern OpCode} {op : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (hpattern : pattern ctx op = some (newCtx, some (newOps, newValues)))
    {hr1 : pattern.ReturnValuesInBounds} {hr2 : pattern.ReturnValues}
    {hr3 : pattern.ReturnCtxChanges}
    {v : ValuePtr} (vIn : v.InBounds ctx.raw) (hmem : v ∈ op.getOperands! ctx.raw) :
    (LocalRewritePattern.mapping hpattern hr1 hr2 hr3 ⟨v, vIn⟩).val = v := by
  unfold LocalRewritePattern.mapping
  have hnotres : v ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl v hmem
  simp [hnotres]

namespace RISCV

variable (src dst : Riscv) (hd : Riscv.propertiesOf dst = RISCVImmediateProperties) (lo hi : Int)

/--
  Characterizes a successful firing of `fold_binop_li`: it must have matched
  `src`/`li`, passed the range check, and created a single `dst` op, returning
  that op and its result. The bound `[lo, hi]` plays no role in the structural
  facts, so all of the predicate proofs below hold uniformly — which is exactly
  what lets the imm5 and imm6 families share this work.
-/
theorem fold_binop_li_spec
    {ctx newCtx : WfIRContext OpCode} {op : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : fold_binop_li src dst hd lo hi ctx op = some (newCtx, some (newOps, newValues))) :
    ∃ reg rhs imm hoper newOp,
      matchRiscvBinop src op ctx = some (reg, rhs) ∧
      matchLi rhs ctx = some imm ∧
      WfRewriter.createOp ctx (.riscv dst) #[RegisterType.mk] #[reg] #[] #[]
          (cast hd.symm imm) none hoper = some (newCtx, newOp) ∧
      newOps = #[newOp] ∧ newValues = #[(newOp.getResult 0 : ValuePtr)] := by
  unfold fold_binop_li at h
  repeat' split at h
  all_goals try (exfalso; simp_all; done)
  rename_i reg rhs hbinop _x imm hmatchli _hbound
  obtain ⟨⟨c, newOp⟩, hcreate, hval⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hval
  obtain ⟨rfl, hops, hvals⟩ := hval
  exact ⟨reg, rhs, imm, _, newOp, hbinop, hmatchli, hcreate, hops.symm, hvals.symm⟩

/--
  `CreatesOneOp pattern` says: whenever `pattern` fires, the matched op has a single
  result, and the rewrite replaces it with exactly one freshly-created op (one result
  register, no blocks or regions, not yet inserted) — returning that op and its result.
  Every combine in this file has this shape; it is all the structural reasoning needs.
-/
def CreatesOneOp (pattern : LocalRewritePattern OpCode) : Prop :=
  ∀ (ctx : WfIRContext OpCode) (op : OperationPtr) (newCtx : WfIRContext OpCode)
    (newOps : Array OperationPtr) (newValues : Array ValuePtr),
    pattern ctx op = some (newCtx, some (newOps, newValues)) →
    op.getNumResults! ctx.raw = 1 ∧
    ∃ (opType : OpCode) (operands : Array ValuePtr) (props : propertiesOf opType)
      (hoper : ∀ oper ∈ operands, oper.InBounds ctx.raw) (newOp : OperationPtr),
      WfRewriter.createOp ctx opType #[RegisterType.mk] operands #[] #[] props none hoper
        = some (newCtx, newOp) ∧
      newOps = #[newOp] ∧ newValues = #[(newOp.getResult 0 : ValuePtr)]

/--
  The four structural `PreservesSemantics` prerequisites hold for any `CreatesOneOp`
  pattern. This is where the structural reasoning lives — once, rather than per combine.
-/
theorem CreatesOneOp.returnPredicates {pattern : LocalRewritePattern OpCode}
    (h : CreatesOneOp pattern) :
    pattern.ReturnCtxChanges ∧ pattern.ReturnValues ∧
      pattern.ReturnValuesInBounds ∧ pattern.ReturnOps := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ctx op newCtx newOps newValues hpat
    obtain ⟨_, _, _, _, _, _, hcreate, _, _⟩ := h ctx op newCtx newOps newValues hpat
    exact WfIRContext.WithCreatedOps.CreatedOp ctx ctx newCtx (.Nil ctx)
      ⟨_, _, _, _, _, _, _, _, _, _, hcreate⟩
  · intro ctx op _hin newCtx newOps newValues hpat
    obtain ⟨hnum, _, _, _, _, _, _, _, hvals⟩ := h ctx op newCtx newOps newValues hpat
    subst hvals; simp [hnum]
  · intro ctx op newCtx newOps newValues hpat v hv
    obtain ⟨_, _, _, _, _, newOp, hcreate, _, hvals⟩ := h ctx op newCtx newOps newValues hpat
    subst hvals; simp only [Array.mem_singleton] at hv; subst hv
    grind [WfRewriter.createOp, Rewriter.createOp_inBounds,
      OperationPtr.getResult_op, OperationPtr.getResult_index]
  · intro ctx op newCtx newOps newValues hpat newOp'
    obtain ⟨_, _, _, _, _, newOp, hcreate, hops, _⟩ := h ctx op newCtx newOps newValues hpat
    subst hops; simp only [Array.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨WfRewriter.createOp_new_inBounds _ hcreate,
             WfRewriter.createOp_new_not_inBounds _ hcreate⟩
    · rintro ⟨_, _⟩
      grind [WfRewriter.createOp, Rewriter.createOp_inBounds]

/-- `fold_binop_li` creates a single `dst` op, replacing the matched (one-result) `src` op. -/
theorem fold_binop_li_createsOneOp : CreatesOneOp (fold_binop_li src dst hd lo hi) := by
  intro ctx op newCtx newOps newValues hpat
  obtain ⟨reg, rhs, imm, hoper, newOp, hbinop, hmatchli, hcreate, hops, hvals⟩ :=
    fold_binop_li_spec src dst hd lo hi hpat
  exact ⟨matchRiscvBinop_getNumResults hbinop, _, _, _, _, newOp, hcreate, hops, hvals⟩

theorem fold_binop_li_ReturnCtxChanges : (fold_binop_li src dst hd lo hi).ReturnCtxChanges :=
  (fold_binop_li_createsOneOp src dst hd lo hi).returnPredicates.1
theorem fold_binop_li_ReturnValues : (fold_binop_li src dst hd lo hi).ReturnValues :=
  (fold_binop_li_createsOneOp src dst hd lo hi).returnPredicates.2.1
theorem fold_binop_li_ReturnValuesInBounds : (fold_binop_li src dst hd lo hi).ReturnValuesInBounds :=
  (fold_binop_li_createsOneOp src dst hd lo hi).returnPredicates.2.2.1
theorem fold_binop_li_ReturnOps : (fold_binop_li src dst hd lo hi).ReturnOps :=
  (fold_binop_li_createsOneOp src dst hd lo hi).returnPredicates.2.2.2

/-! ### imm5 / imm6 specializations — the same proofs at different bounds. -/

theorem fold_shift5_li_ReturnCtxChanges : (fold_shift5_li src dst hd).ReturnCtxChanges :=
  fold_binop_li_ReturnCtxChanges src dst hd 0 31
theorem fold_shift5_li_ReturnValues : (fold_shift5_li src dst hd).ReturnValues :=
  fold_binop_li_ReturnValues src dst hd 0 31
theorem fold_shift5_li_ReturnValuesInBounds : (fold_shift5_li src dst hd).ReturnValuesInBounds :=
  fold_binop_li_ReturnValuesInBounds src dst hd 0 31
theorem fold_shift5_li_ReturnOps : (fold_shift5_li src dst hd).ReturnOps :=
  fold_binop_li_ReturnOps src dst hd 0 31

theorem fold_shift6_li_ReturnCtxChanges : (fold_shift6_li src dst hd).ReturnCtxChanges :=
  fold_binop_li_ReturnCtxChanges src dst hd 0 63
theorem fold_shift6_li_ReturnValues : (fold_shift6_li src dst hd).ReturnValues :=
  fold_binop_li_ReturnValues src dst hd 0 63
theorem fold_shift6_li_ReturnValuesInBounds : (fold_shift6_li src dst hd).ReturnValuesInBounds :=
  fold_binop_li_ReturnValuesInBounds src dst hd 0 63
theorem fold_shift6_li_ReturnOps : (fold_shift6_li src dst hd).ReturnOps :=
  fold_binop_li_ReturnOps src dst hd 0 63

/-! ### Structural predicates for `fold_zextw_slli_to_slliuw` -/

/-- Characterizes a successful firing of `fold_zextw_slli_to_slliuw`: it matched a
    `slli` whose operand is a `zextw`, and created a single `slliuw`. -/
theorem fold_zextw_slli_to_slliuw_spec
    {ctx newCtx : WfIRContext OpCode} {op : OperationPtr}
    {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    (h : fold_zextw_slli_to_slliuw ctx op = some (newCtx, some (newOps, newValues))) :
    ∃ operands shamt x hoper newOp,
      matchOp op ctx (.riscv .slli) 1 = some (operands, shamt) ∧
      matchZextw operands[0]! ctx = some x ∧
      WfRewriter.createOp ctx (.riscv .slliuw) #[RegisterType.mk] #[x] #[] #[] shamt none hoper
        = some (newCtx, newOp) ∧
      newOps = #[newOp] ∧ newValues = #[(newOp.getResult 0 : ValuePtr)] := by
  unfold fold_zextw_slli_to_slliuw at h
  repeat' split at h
  all_goals try (exfalso; simp_all; done)
  rename_i _s operands shamt hslli xz hzext
  obtain ⟨⟨c, newOp⟩, hcreate, hval⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hval
  obtain ⟨rfl, hops, hvals⟩ := hval
  exact ⟨operands, shamt, xz, _, newOp, hslli, hzext, hcreate, hops.symm, hvals.symm⟩

theorem fold_zextw_slli_to_slliuw_createsOneOp : CreatesOneOp fold_zextw_slli_to_slliuw := by
  intro ctx op newCtx newOps newValues hpat
  obtain ⟨operands, shamt, x, hoper, newOp, hslli, hzext, hcreate, hops, hvals⟩ :=
    fold_zextw_slli_to_slliuw_spec hpat
  exact ⟨matchOp_getNumResults hslli, _, _, _, _, newOp, hcreate, hops, hvals⟩

theorem fold_zextw_slli_to_slliuw_ReturnCtxChanges : fold_zextw_slli_to_slliuw.ReturnCtxChanges :=
  fold_zextw_slli_to_slliuw_createsOneOp.returnPredicates.1
theorem fold_zextw_slli_to_slliuw_ReturnValues : fold_zextw_slli_to_slliuw.ReturnValues :=
  fold_zextw_slli_to_slliuw_createsOneOp.returnPredicates.2.1
theorem fold_zextw_slli_to_slliuw_ReturnValuesInBounds :
    fold_zextw_slli_to_slliuw.ReturnValuesInBounds :=
  fold_zextw_slli_to_slliuw_createsOneOp.returnPredicates.2.2.1
theorem fold_zextw_slli_to_slliuw_ReturnOps : fold_zextw_slli_to_slliuw.ReturnOps :=
  fold_zextw_slli_to_slliuw_createsOneOp.returnPredicates.2.2.2

end RISCV

end Veir

namespace Veir.Data.RISCV


/--
  Prove the correctness of the `right_identity_zero_add` combine.
-/
theorem right_identity_zero_add:
    (RISCV.add lhs (Data.RISCV.li (BitVec.ofInt 64 0))) = lhs := by
  simp [reg_toBitVec]

/--
  Encoding fact: re-encoding an `Int` immediate at width 5 agrees with
  truncating its width-64 encoding to 5 bits. This connects how the Veir
  interpreter materializes the same `properties.value.value` for `riscv.li`
  (via `BitVec.ofInt 64`) and for `riscv.slliw` (via `BitVec.ofInt 5`).
-/
theorem ofInt5_eq_setWidth_ofInt64 (i : Int) :
    BitVec.ofInt 5 i = (BitVec.ofInt 64 i).setWidth 5 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  omega

/--
  Correctness of the `fold_sllw_li_to_slliw` combine.

  The Veir interpreter evaluates the source `riscv.sllw rs1 (riscv.li i)` as
  `RISCV.sllw (RISCV.li (BitVec.ofInt 64 i)) rs1` and the rewritten
  `riscv.slliw rs1 i` as `RISCV.slliw (BitVec.ofInt 5 i) rs1`, where `i` is the
  shared immediate `properties.value.value`. We prove these denote the same
  register value for every register `rs1` and every immediate `i` — i.e. the new
  `slliw` refines (in fact, equals) the original `sllw`/`li` pair. Note this holds
  unconditionally: both instructions only consult the low 5 bits of the shift
  amount, so the combine's `0 ≤ i ≤ 31` guard is needed only for encodability,
  not for value correctness.
-/
theorem fold_sllw_li_to_slliw (rs1 : Reg) (i : Int) :
    RISCV.sllw (RISCV.li (BitVec.ofInt 64 i)) rs1
      = RISCV.slliw (BitVec.ofInt 5 i) rs1 := by
  rw [ofInt5_eq_setWidth_ofInt64]
  simp only [reg_toBitVec]
  bv_decide

/-- The other imm5 semantic equalities (same `ofInt5`-truncation + `bv_decide` as `sllw`). -/
theorem fold_srlw_li_to_srliw (rs1 : Reg) (i : Int) :
    RISCV.srlw (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.srliw (BitVec.ofInt 5 i) rs1 := by
  rw [ofInt5_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide

theorem fold_sraw_li_to_sraiw (rs1 : Reg) (i : Int) :
    RISCV.sraw (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.sraiw (BitVec.ofInt 5 i) rs1 := by
  rw [ofInt5_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide

theorem fold_rorw_li_to_roriw (rs1 : Reg) (i : Int) :
    RISCV.rorw (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.roriw (BitVec.ofInt 5 i) rs1 := by
  rw [ofInt5_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide

/-- The width-6 encoding fact, for the imm6 family. -/
theorem ofInt6_eq_setWidth_ofInt64 (i : Int) :
    BitVec.ofInt 6 i = (BitVec.ofInt 64 i).setWidth 6 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  omega

/-- The imm6 semantic equalities: full-width shifts/rotates and single-bit ops, `ofInt6`. -/
theorem fold_sll_li_to_slli (rs1 : Reg) (i : Int) :
    RISCV.sll (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.slli (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide
theorem fold_srl_li_to_srli (rs1 : Reg) (i : Int) :
    RISCV.srl (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.srli (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide
theorem fold_sra_li_to_srai (rs1 : Reg) (i : Int) :
    RISCV.sra (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.srai (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide
theorem fold_ror_li_to_rori (rs1 : Reg) (i : Int) :
    RISCV.ror (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.rori (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide
theorem fold_bclr_li_to_bclri (rs1 : Reg) (i : Int) :
    RISCV.bclr (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.bclri (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide
theorem fold_bext_li_to_bexti (rs1 : Reg) (i : Int) :
    RISCV.bext (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.bexti (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide
theorem fold_binv_li_to_binvi (rs1 : Reg) (i : Int) :
    RISCV.binv (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.binvi (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide
theorem fold_bset_li_to_bseti (rs1 : Reg) (i : Int) :
    RISCV.bset (RISCV.li (BitVec.ofInt 64 i)) rs1 = RISCV.bseti (BitVec.ofInt 6 i) rs1 := by
  rw [ofInt6_eq_setWidth_ofInt64]; simp only [reg_toBitVec]; bv_decide

/--
  Correctness of the `fold_zextw_slli_to_slliuw` combine.

  The Veir interpreter evaluates the source `riscv.slli (riscv.zextw x) i` as
  `RISCV.slli (BitVec.ofInt 6 i) (RISCV.zextw x)` and the rewritten
  `riscv.slliuw x i` as `RISCV.slliuw (BitVec.ofInt 6 i) x` (both immediates come
  from the same shared property, materialized via `BitVec.ofInt 6`). We prove
  these denote the same register value for every register `x` and shift amount
  `shamt` — both compute `zeroExtend64(low32(x)) <<< shamt`.
-/
theorem fold_zextw_slli_to_slliuw (x : Reg) (shamt : BitVec 6) :
    RISCV.slli shamt (RISCV.zextw x) = RISCV.slliuw shamt x := by
  simp only [reg_toBitVec]
  bv_decide

end Veir.Data.RISCV

namespace Veir.RISCV

open Data.RISCV (Reg)

/-! ## The keystone, generalized

  `fold_binop_li_PreservesSemantics_of` proves `PreservesSemantics` for the whole `fold_binop_li`
  family from three per-opcode "leaf" facts: how the source op evaluates (`hsrc`), how the
  destination op evaluates (`hdst`), and that the two agree on the matched `li` immediate (`hsem`).
  The structural reasoning — equation-lemma extraction, operand plumbing, refinement transfer —
  lives here once; each combine instantiates it with its interpreter computations and bitvector
  equality. -/
theorem fold_binop_li_PreservesSemantics_of
    (src dst : Riscv) (hd : Riscv.propertiesOf dst = RISCVImmediateProperties) (lo hi : Int)
    (srcF : Reg → Reg → Reg) (dstF : HasOpInfo.propertiesOf (OpCode.riscv dst) → Reg → Reg)
    (hsrc : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {ov : Array RuntimeValue} {mem res},
      op.getOpType! ctx = OpCode.riscv src → op.interpret ctx ov mem = some res →
      ∃ o1 o2 : Reg, ov = #[.reg o1, .reg o2] ∧ res = .ok (#[.reg (srcF o1 o2)], mem, none))
    (hdst : ∀ {op : OperationPtr} {ctx : IRContext OpCode} {o1 : Reg} {mem}
      (p : HasOpInfo.propertiesOf (OpCode.riscv dst)),
      op.getOpType! ctx = OpCode.riscv dst → op.getProperties! ctx (OpCode.riscv dst) = p →
      op.interpret ctx #[.reg o1] mem = some (.ok (#[.reg (dstF p o1)], mem, none)))
    (hsem : ∀ (o1 : Reg) (imm : HasOpInfo.propertiesOf (OpCode.riscv .li)),
      srcF o1 (Data.RISCV.li (BitVec.ofInt 64 imm.value.value)) = dstF (cast hd.symm imm) o1) :
    LocalRewritePattern.PreservesSemantics (fold_binop_li src dst hd lo hi)
      (fold_binop_li_ReturnOps src dst hd lo hi) (fold_binop_li_ReturnCtxChanges src dst hd lo hi)
      (fold_binop_li_ReturnValuesInBounds src dst hd lo hi) (fold_binop_li_ReturnValues src dst hd lo hi) := by
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern
        state hstateEq newState cf hinterpop sourceValues hsource state' hstate'Eq href
  obtain ⟨reg, rhs, imm, hoper, newOp, hbinop, hmatchli, hcreate, hopsEq, hvalsEq⟩ :=
    fold_binop_li_spec src dst hd lo hi hpattern
  obtain ⟨hopTy, hopOperands⟩ := matchRiscvBinop_getOperands hbinop
  have hopNumRes : op.getNumResults! ctx.raw = 1 := matchRiscvBinop_getNumResults hbinop
  have hrhsmem : rhs ∈ op.getOperands! ctx.raw := by rw [hopOperands]; simp
  have hregmem : reg ∈ op.getOperands! ctx.raw := by rw [hopOperands]; simp
  have hcval := getVar_li_of_equationLemma ctxDom opInBounds hstateEq hrhsmem hmatchli
  obtain ⟨operandValues, resValues, mem', newVars, hov, hinterp', hset, hnewstate⟩ :=
    interpretOp_some_iff.mp hinterpop
  obtain ⟨o1, o2, hovEq, hresEq⟩ := hsrc hopTy hinterp'
  obtain ⟨va, vb, hgetReg, hgetRhs, hovEq2⟩ := getOperandValues_pair_inv hopOperands hov
  have hvavb : (#[va, vb] : Array RuntimeValue) = #[.reg o1, .reg o2] := by rw [← hovEq2, hovEq]
  have hva : va = RuntimeValue.reg o1 := by have := congrArg (·[0]!) hvavb; simpa using this
  have hvb : vb = RuntimeValue.reg o2 := by have := congrArg (·[1]!) hvavb; simpa using this
  have hcval' : vb = RuntimeValue.reg (Data.RISCV.li (BitVec.ofInt 64 imm.value.value)) := by
    rw [hgetRhs] at hcval; exact Option.some.inj hcval
  have ho2 : o2 = Data.RISCV.li (BitVec.ofInt 64 imm.value.value) := by
    rw [hvb] at hcval'; exact RuntimeValue.reg.inj hcval'
  obtain ⟨hresVals, hmem'eq, hcfeq⟩ :
      resValues = #[RuntimeValue.reg (srcF o1 o2)] ∧ mem' = state.memory ∧ cf = none := by
    have := hresEq; simp only [UBOr.ok.injEq, Prod.mk.injEq] at this; grind
  have hresIn : (ValuePtr.opResult (op.getResult 0)).InBounds ctx.raw := by
    rw [ValuePtr.inBounds_opResult]
    grind [OpResultPtr.inBounds_def, OperationPtr.getResult_op, OperationPtr.getResult_index,
      OperationPtr.getNumResults!_eq_getNumResults]
  have hgetResOp : newState.variables.getVar? (ValuePtr.opResult (op.getResult 0))
      = some (.reg (srcF o1 o2)) := by
    rw [hnewstate, VariableState.getVar?_setResultValues?_of_value_inBounds
        (value := ValuePtr.opResult (op.getResult 0)) hresIn hset]
    simp [OperationPtr.getResult_op, OperationPtr.getResult_index, hresVals]
  have hsrcEq : sourceValues = #[RuntimeValue.reg (srcF o1 o2)] := by
    rw [show op.getResults ctx.raw = #[(op.getResult 0 : ValuePtr)] from by
      rw [← OperationPtr.getResults!_eq_getResults opInBounds, getResults!_single hopNumRes]] at hsource
    simp [Array.mapM_eq_mapM_toList, hgetResOp] at hsource
    exact hsource.symm
  have hregIn : reg.InBounds ctx.raw :=
    OperationPtr.getOperands!_inBounds ctx.wellFormed.inBounds opInBounds hregmem
  have hnotres : reg ∉ op.getResults! ctx.raw :=
    IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      OperationPtr.dominates_refl reg hregmem
  obtain ⟨tval, htval, hreftval⟩ := href.2 reg hregIn va hgetReg
  simp only [LocalRewritePattern.mapping, dif_neg hnotres] at htval
  rw [hva] at hreftval
  have htvalEq : tval = RuntimeValue.reg o1 := by cases tval <;> simp_all [RuntimeValue.isRefinedBy]
  rw [htvalEq] at htval
  have hnewOpIn : newOp.InBounds newCtx.raw := WfRewriter.createOp_new_inBounds _ hcreate
  have hnewTy : newOp.getOpType! newCtx.raw = OpCode.riscv dst := by
    have := OperationPtr.getOpType!_WfRewriter_createOp (operation := newOp) hcreate; simpa using this
  have hnewProps : newOp.getProperties! newCtx.raw (OpCode.riscv dst) = cast hd.symm imm := by
    have h := OperationPtr.getProperties!_WfRewriter_createOp (operation := newOp) hcreate
    simp only [↓reduceIte] at h; exact h
  have hnewOperands : newOp.getOperands! newCtx.raw = #[reg] := by
    have := OperationPtr.getOperands!_WfRewriter_createOp (operation := newOp) hcreate; simpa using this
  have hovTgt : state'.variables.getOperandValues newOp = some #[RuntimeValue.reg o1] :=
    getOperandValues_single hnewOperands htval
  have hinterpTgt : newOp.interpret newCtx.raw #[.reg o1] state'.memory
      = some (.ok (#[.reg (dstF (cast hd.symm imm) o1)], state'.memory, none)) :=
    hdst (cast hd.symm imm) hnewTy hnewProps
  have hconf : RuntimeValue.ArrayConforms #[RuntimeValue.reg (dstF (cast hd.symm imm) o1)]
      (newOp.getResultTypes! newCtx.raw) := by
    have hrt := OperationPtr.getResultTypes!_WfRewriter_createOp (operation := newOp) hcreate
    simp only [↓reduceIte] at hrt
    rw [hrt]; refine ⟨by simp, fun i hi => ?_⟩
    simp only [Array.size_singleton] at hi
    match i, hi with | 0, _ => simp [RuntimeValue.Conforms]
  obtain ⟨newVars', hsetTgt⟩ :=
    (VariableState.setResultValues?_isSome_iff_conforms (inBounds := hnewOpIn)).mp hconf
  have hinterpOpTgt : interpretOp newOp state' = some (.ok (⟨newVars', state'.memory⟩, none)) := by
    rw [interpretOp_some_iff]; exact ⟨_, _, _, _, hovTgt, hinterpTgt, hsetTgt, rfl⟩
  subst hopsEq hvalsEq
  refine ⟨⟨newVars', state'.memory⟩, ?_, ?_, #[RuntimeValue.reg (dstF (cast hd.symm imm) o1)], ?_, ?_⟩
  · subst hcfeq; simp [interpretOpList_cons, hinterpOpTgt]; rfl
  · rw [hnewstate]; simp [hmem'eq]; exact href.1
  · simp only [Array.mapM_eq_mapM_toList]
    have hresInTgt : (ValuePtr.opResult (newOp.getResult 0)).InBounds newCtx.raw := by
      rw [ValuePtr.inBounds_opResult]
      grind [OpResultPtr.inBounds_def, OperationPtr.getResult_op, OperationPtr.getResult_index,
        OperationPtr.getNumResults!_eq_getNumResults, OperationPtr.getNumResults!_WfRewriter_createOp]
    have hgetTgt : newVars'.getVar? (ValuePtr.opResult (newOp.getResult 0))
        = some (.reg (dstF (cast hd.symm imm) o1)) := by
      rw [VariableState.getVar?_setResultValues?_of_value_inBounds
          (value := ValuePtr.opResult (newOp.getResult 0)) hresInTgt hsetTgt]
      simp [OperationPtr.getResult_op, OperationPtr.getResult_index]
    simp [hgetTgt]
  · rw [hsrcEq, ho2]
    refine ⟨by simp, fun i hi => ?_⟩
    simp only [Array.size_singleton] at hi
    match i, hi with
    | 0, _ => simp [RuntimeValue.isRefinedBy, hsem o1 imm]

/-- `fold_sllw_li_to_slliw` preserves semantics (instantiation of the generic theorem). -/
theorem fold_sllw_li_to_slliw_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_sllw_li_to_slliw
      (fold_shift5_li_ReturnOps .sllw .slliw rfl) (fold_shift5_li_ReturnCtxChanges .sllw .slliw rfl)
      (fold_shift5_li_ReturnValuesInBounds .sllw .slliw rfl) (fold_shift5_li_ReturnValues .sllw .slliw rfl) :=
  fold_binop_li_PreservesSemantics_of .sllw .slliw rfl 0 31
    (fun o1 o2 => Data.RISCV.sllw o2 o1)
    (fun p o1 => Data.RISCV.slliw (BitVec.ofInt 5 p.value.value) o1)
    (fun hty h => sllw_interpret_inv hty h)
    (fun _ hty hp => slliw_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_sllw_li_to_slliw o1 imm.value.value)

theorem fold_srlw_li_to_srliw_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_srlw_li_to_srliw
      (fold_shift5_li_ReturnOps .srlw .srliw rfl) (fold_shift5_li_ReturnCtxChanges .srlw .srliw rfl)
      (fold_shift5_li_ReturnValuesInBounds .srlw .srliw rfl) (fold_shift5_li_ReturnValues .srlw .srliw rfl) :=
  fold_binop_li_PreservesSemantics_of .srlw .srliw rfl 0 31
    (fun o1 o2 => Data.RISCV.srlw o2 o1)
    (fun p o1 => Data.RISCV.srliw (BitVec.ofInt 5 p.value.value) o1)
    (fun hty h => srlw_interpret_inv hty h)
    (fun _ hty hp => srliw_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_srlw_li_to_srliw o1 imm.value.value)

theorem fold_sraw_li_to_sraiw_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_sraw_li_to_sraiw
      (fold_shift5_li_ReturnOps .sraw .sraiw rfl) (fold_shift5_li_ReturnCtxChanges .sraw .sraiw rfl)
      (fold_shift5_li_ReturnValuesInBounds .sraw .sraiw rfl) (fold_shift5_li_ReturnValues .sraw .sraiw rfl) :=
  fold_binop_li_PreservesSemantics_of .sraw .sraiw rfl 0 31
    (fun o1 o2 => Data.RISCV.sraw o2 o1)
    (fun p o1 => Data.RISCV.sraiw (BitVec.ofInt 5 p.value.value) o1)
    (fun hty h => sraw_interpret_inv hty h)
    (fun _ hty hp => sraiw_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_sraw_li_to_sraiw o1 imm.value.value)

theorem fold_rorw_li_to_roriw_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_rorw_li_to_roriw
      (fold_shift5_li_ReturnOps .rorw .roriw rfl) (fold_shift5_li_ReturnCtxChanges .rorw .roriw rfl)
      (fold_shift5_li_ReturnValuesInBounds .rorw .roriw rfl) (fold_shift5_li_ReturnValues .rorw .roriw rfl) :=
  fold_binop_li_PreservesSemantics_of .rorw .roriw rfl 0 31
    (fun o1 o2 => Data.RISCV.rorw o2 o1)
    (fun p o1 => Data.RISCV.roriw (BitVec.ofInt 5 p.value.value) o1)
    (fun hty h => rorw_interpret_inv hty h)
    (fun _ hty hp => roriw_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_rorw_li_to_roriw o1 imm.value.value)


/-! ## imm6 family `PreservesSemantics` (instantiations of the generic theorem). -/

theorem fold_sll_li_to_slli_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_sll_li_to_slli
      (fold_shift6_li_ReturnOps .sll .slli rfl) (fold_shift6_li_ReturnCtxChanges .sll .slli rfl)
      (fold_shift6_li_ReturnValuesInBounds .sll .slli rfl) (fold_shift6_li_ReturnValues .sll .slli rfl) :=
  fold_binop_li_PreservesSemantics_of .sll .slli rfl 0 63
    (fun o1 o2 => Data.RISCV.sll o2 o1)
    (fun p o1 => Data.RISCV.slli (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => sll_interpret_inv hty h)
    (fun _ hty hp => slli_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_sll_li_to_slli o1 imm.value.value)

theorem fold_srl_li_to_srli_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_srl_li_to_srli
      (fold_shift6_li_ReturnOps .srl .srli rfl) (fold_shift6_li_ReturnCtxChanges .srl .srli rfl)
      (fold_shift6_li_ReturnValuesInBounds .srl .srli rfl) (fold_shift6_li_ReturnValues .srl .srli rfl) :=
  fold_binop_li_PreservesSemantics_of .srl .srli rfl 0 63
    (fun o1 o2 => Data.RISCV.srl o2 o1)
    (fun p o1 => Data.RISCV.srli (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => srl_interpret_inv hty h)
    (fun _ hty hp => srli_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_srl_li_to_srli o1 imm.value.value)

theorem fold_sra_li_to_srai_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_sra_li_to_srai
      (fold_shift6_li_ReturnOps .sra .srai rfl) (fold_shift6_li_ReturnCtxChanges .sra .srai rfl)
      (fold_shift6_li_ReturnValuesInBounds .sra .srai rfl) (fold_shift6_li_ReturnValues .sra .srai rfl) :=
  fold_binop_li_PreservesSemantics_of .sra .srai rfl 0 63
    (fun o1 o2 => Data.RISCV.sra o2 o1)
    (fun p o1 => Data.RISCV.srai (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => sra_interpret_inv hty h)
    (fun _ hty hp => srai_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_sra_li_to_srai o1 imm.value.value)

theorem fold_ror_li_to_rori_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_ror_li_to_rori
      (fold_shift6_li_ReturnOps .ror .rori rfl) (fold_shift6_li_ReturnCtxChanges .ror .rori rfl)
      (fold_shift6_li_ReturnValuesInBounds .ror .rori rfl) (fold_shift6_li_ReturnValues .ror .rori rfl) :=
  fold_binop_li_PreservesSemantics_of .ror .rori rfl 0 63
    (fun o1 o2 => Data.RISCV.ror o2 o1)
    (fun p o1 => Data.RISCV.rori (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => ror_interpret_inv hty h)
    (fun _ hty hp => rori_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_ror_li_to_rori o1 imm.value.value)

theorem fold_bclr_li_to_bclri_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_bclr_li_to_bclri
      (fold_shift6_li_ReturnOps .bclr .bclri rfl) (fold_shift6_li_ReturnCtxChanges .bclr .bclri rfl)
      (fold_shift6_li_ReturnValuesInBounds .bclr .bclri rfl) (fold_shift6_li_ReturnValues .bclr .bclri rfl) :=
  fold_binop_li_PreservesSemantics_of .bclr .bclri rfl 0 63
    (fun o1 o2 => Data.RISCV.bclr o2 o1)
    (fun p o1 => Data.RISCV.bclri (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => bclr_interpret_inv hty h)
    (fun _ hty hp => bclri_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_bclr_li_to_bclri o1 imm.value.value)

theorem fold_bext_li_to_bexti_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_bext_li_to_bexti
      (fold_shift6_li_ReturnOps .bext .bexti rfl) (fold_shift6_li_ReturnCtxChanges .bext .bexti rfl)
      (fold_shift6_li_ReturnValuesInBounds .bext .bexti rfl) (fold_shift6_li_ReturnValues .bext .bexti rfl) :=
  fold_binop_li_PreservesSemantics_of .bext .bexti rfl 0 63
    (fun o1 o2 => Data.RISCV.bext o2 o1)
    (fun p o1 => Data.RISCV.bexti (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => bext_interpret_inv hty h)
    (fun _ hty hp => bexti_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_bext_li_to_bexti o1 imm.value.value)

theorem fold_binv_li_to_binvi_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_binv_li_to_binvi
      (fold_shift6_li_ReturnOps .binv .binvi rfl) (fold_shift6_li_ReturnCtxChanges .binv .binvi rfl)
      (fold_shift6_li_ReturnValuesInBounds .binv .binvi rfl) (fold_shift6_li_ReturnValues .binv .binvi rfl) :=
  fold_binop_li_PreservesSemantics_of .binv .binvi rfl 0 63
    (fun o1 o2 => Data.RISCV.binv o2 o1)
    (fun p o1 => Data.RISCV.binvi (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => binv_interpret_inv hty h)
    (fun _ hty hp => binvi_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_binv_li_to_binvi o1 imm.value.value)

theorem fold_bset_li_to_bseti_PreservesSemantics :
    LocalRewritePattern.PreservesSemantics fold_bset_li_to_bseti
      (fold_shift6_li_ReturnOps .bset .bseti rfl) (fold_shift6_li_ReturnCtxChanges .bset .bseti rfl)
      (fold_shift6_li_ReturnValuesInBounds .bset .bseti rfl) (fold_shift6_li_ReturnValues .bset .bseti rfl) :=
  fold_binop_li_PreservesSemantics_of .bset .bseti rfl 0 63
    (fun o1 o2 => Data.RISCV.bset o2 o1)
    (fun p o1 => Data.RISCV.bseti (BitVec.ofInt 6 p.value.value) o1)
    (fun hty h => bset_interpret_inv hty h)
    (fun _ hty hp => bseti_interpret_eq hty hp)
    (fun o1 imm => Data.RISCV.fold_bset_li_to_bseti o1 imm.value.value)

end Veir.RISCV
