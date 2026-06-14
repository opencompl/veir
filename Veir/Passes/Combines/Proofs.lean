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
