import Veir.PatternRewriter.Basic
import Veir.Interpreter
import Veir.IR.WellFormed
import Veir.Passes.Matching
import Veir.Rewriter.WfRewriter
import Veir.PatternRewriter.Semantics
import Veir.Verifier
import Veir.Data.LLVM.Int.Lemmas
import Veir.Data.RISCV.Reg.Lemmas
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm
import Veir.Passes.InstructionSelection.RewriteProofs.LowerBexti

namespace Veir

/-- `llvm.shl` is pure. -/
theorem OperationPtr.Pure.llvm_shl {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .shl) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

/-- `llvm.and` is pure. -/
theorem OperationPtr.Pure.llvm_and {op : OperationPtr} {ctx : IRContext OpCode}
    (hType : op.getOpType! ctx = .llvm .and) : op.Pure ctx := by
  unfold OperationPtr.Pure
  rw [hType]
  intro operands memory₁ memory₂
  simp only [interpretOp', Llvm.interpretOp']
  repeat' split
  all_goals first
    | rfl
    | simp [Interp.map, Option.map, UBOr.map, pure, bind, Option.bind]

theorem shl_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {lhs x shamt : ValuePtr} {shrOp : OperationPtr}
    {shProps : propertiesOf (.llvm .shl)} {shAttr : IntegerAttr} {intType : IntegerType}
    (hDef : getDefiningOp lhs ctx.raw = some shrOp)
    (hLshr : matchShl shrOp ctx.raw = some (x, shamt, shProps))
    (hShConst : matchConstantIntVal shamt ctx.raw = some shAttr)
    (hOperand : lhs ∈ op.getOperands! ctx.raw)
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ xv, state.variables.getVar? x = some (RuntimeValue.int intType.bitwidth xv) ∧
      state.variables.getVar? lhs = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.shl xv (Data.LLVM.Int.constant intType.bitwidth shAttr.value) shProps.nsw shProps.nuw)) ∧
      (x.getType! ctx.raw).val = Attribute.integerType intType ∧
      x.dominatesIp (InsertPoint.before op) ctx ∧
      x.InBounds ctx.raw ∧
      x ∉ op.getResults! ctx.raw := by
  -- Syntactic facts from the matches.
  obtain ⟨lhsPtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hShrType, hShrNumResults, hShrOperands, hShProps⟩ := matchShl_implies hLshr
  obtain ⟨shamtPtr, rfl, hShamtOp⟩ := matchConstantIntVal_implies hShConst
  obtain ⟨hShamtType, hShamtProps⟩ := matchConstantIntOp_implies hShamtOp
  have hLhsIn : (ValuePtr.opResult lhsPtr).InBounds ctx.raw := by grind
  have hShrOpIn : lhsPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hlhsIdx : lhsPtr.index < lhsPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hlhsEq : lhsPtr = lhsPtr.op.getResult 0 := by
    have hidx : lhsPtr.index = 0 := by omega
    cases lhsPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  -- The `lshr` verifies as `LLVMShift`.
  have hShrVerified : lhsPtr.op.Verified ctx hShrOpIn := by grind
  obtain ⟨-, -, hShrResEqOp0, intType2, hShrOp1Type⟩ :=
    OperationPtr.Verified.llvm_shl hShrVerified hShrType
  have hVTypeEq : (ValuePtr.opResult lhsPtr).getType! ctx.raw
      = ((lhsPtr.op.getResult 0).get! ctx.raw).type := by rw [hlhsEq]; rfl
  -- `x` (operand 0) shares `lhs`'s type `intType`; `shamt` (operand 1) has type `intType2`.
  have hxIdxEq : x = (lhsPtr.op.getOperands! ctx.raw)[0]! := by rw [hShrOperands]; rfl
  have hShamtIdxEq : ValuePtr.opResult shamtPtr = (lhsPtr.op.getOperands! ctx.raw)[1]! := by
    rw [hShrOperands]; rfl
  have hShrOperand0 : lhsPtr.op.getOperand! ctx.raw 0 = x := by
    rw [hxIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hShrOperand1 : lhsPtr.op.getOperand! ctx.raw 1 = ValuePtr.opResult shamtPtr := by
    rw [hShamtIdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hxType : (x.getType! ctx.raw).val = Attribute.integerType intType := by
    have : ((lhsPtr.op.getResult 0).get! ctx.raw).type.val
        = ((lhsPtr.op.getOperand! ctx.raw 0).getType! ctx.raw).val := hShrResEqOp0
    rw [hShrOperand0] at this
    rw [← this, ← hVTypeEq]; exact hLhsType
  have hShamtValType : ((ValuePtr.opResult shamtPtr).getType! ctx.raw).val
      = Attribute.integerType intType2 := by rw [← hShrOperand1, hShrOp1Type]
  -- Dominance: the `lshr` strictly dominates `op`.
  have hShrDefines : (ValuePtr.opResult lhsPtr).getDefiningOp! ctx.raw = some lhsPtr.op := by
    have hOwner := (ctx.wellFormed.operations lhsPtr.op hShrOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hShrSDom : lhsPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hShrDefines hOperand
  have hShrDomIp : lhsPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hShrPure : lhsPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_shl hShrType
  obtain ⟨cfS, hInterpShr⟩ := stateWf lhsPtr.op hShrOpIn hShrPure hShrDomIp
  -- Unfold the `lshr`'s interpretation (recovers the width equality `h'`).
  obtain ⟨xv, sv, h', hxVal, hsVal, -, hShrResVal, -⟩ :=
    matchShiftOp_interpretOp_unfold (srcOp := .shl)
      (shiftFn := fun a b props => Data.LLVM.Int.shl a b props.nsw props.nuw)
      (props := lhsPtr.op.getProperties! ctx.raw (.llvm .shl))
      hShrOpIn hShrType hShrNumResults hShrOperands rfl
      (by intro bw bw' a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp'] at hh
          split at hh
          · exact absurd hh (by simp)
          · rename_i hbw; obtain rfl : bw' = bw := by omega
            refine ⟨rfl, ?_⟩
            simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hh
            grind)
      hInterpShr hxType hShamtValType
  -- The `shamt` constant's structural facts.
  have hShamtIn : (ValuePtr.opResult shamtPtr).InBounds ctx.raw := by
    grind [OperationPtr.getOperands!]
  have hShamtOpIn : shamtPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hShamtVerified : shamtPtr.op.Verified ctx hShamtOpIn := by grind
  obtain ⟨hShamtNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hShamtVerified hShamtType
  have hShamtIdx : shamtPtr.index < shamtPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hShamtEq : shamtPtr = shamtPtr.op.getResult 0 := by
    have hidx : shamtPtr.index = 0 := by omega
    cases shamtPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hShamtResType : ((shamtPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType2, by grind⟩ := by
    have heq : ((ValuePtr.opResult shamtPtr).getType! ctx.raw)
        = ((shamtPtr.op.getResult 0).get! ctx.raw).type := by rw [hShamtEq]; rfl
    apply Subtype.ext; rw [← heq]; exact hShamtValType
  have hShamtDefines : (ValuePtr.opResult shamtPtr).getDefiningOp! ctx.raw = some shamtPtr.op := by
    have hOwner := (ctx.wellFormed.operations shamtPtr.op hShamtOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hShamtSDomShr : shamtPtr.op.strictlyDominates lhsPtr.op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hShamtDefines (by grind [OperationPtr.getOperands!])
  have hShamtSDom : shamtPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hShamtSDomShr hShrSDom
  have hShamtDomIp : shamtPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hShamtPure : shamtPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hShamtType
  obtain ⟨cfC, hInterpShamt⟩ := stateWf shamtPtr.op hShamtOpIn hShamtPure hShamtDomIp
  have hShamtResVal :=
    constantOp_interpretOp_unfold hShamtOpIn hShamtType hShamtNumResults hShamtProps hShamtResType
      hInterpShamt
  have hsvEq : sv = Data.LLVM.Int.constant intType2.bitwidth shAttr.value := by
    rw [hShamtEq] at hsVal; grind
  -- Normalise the width equality: substitute `intType2.bitwidth = intType.bitwidth`.
  subst hsvEq
  obtain ⟨w⟩ := intType; obtain ⟨w2⟩ := intType2
  simp only at h' hxType hxVal ⊢; subst w2
  refine ⟨xv, hxVal, ?_, hxType, ?_, ?_, ?_⟩
  · rw [hShProps, hlhsEq]; exact hShrResVal
  · exact ValuePtr.dominatesIp_before_of_strictlyDominates
      (ctxDom.operand_dominates_op hShrOpIn (by grind [OperationPtr.getOperands!])) hShrSDom
  · grind [OperationPtr.getOperands!]
  · exact IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom
      (OperationPtr.dominates_of_strictlyDominates hShrSDom) x
      (by grind [OperationPtr.getOperands!])

/-- If `m` is defined by an `llvm.and` op, recover `m`'s runtime value as `and` of its two operands'
    values (used to expose the soundness-gate structure `M = and Z mask`). -/
theorem and_getVar?_of_EquationLemmaAt {ctx : WfIRContext OpCode}
    (_ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {m o0 o1 : ValuePtr} {andOp : OperationPtr}
    {andProps : propertiesOf (.llvm .and)} {intType : IntegerType}
    (hDef : getDefiningOp m ctx.raw = some andOp)
    (hAnd : matchAnd andOp ctx.raw = some (o0, o1, andProps))
    (hSDom : andOp.strictlyDominates op ctx) (hmIn : m.InBounds ctx.raw)
    (hMType : (m.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ o0v o1v,
      state.variables.getVar? o0 = some (RuntimeValue.int intType.bitwidth o0v) ∧
      state.variables.getVar? o1 = some (RuntimeValue.int intType.bitwidth o1v) ∧
      state.variables.getVar? m = some (RuntimeValue.int intType.bitwidth
        (Data.LLVM.Int.and o0v o1v)) := by
  obtain ⟨mPtr, rfl, rfl⟩ := getDefiningOp_implies hDef
  obtain ⟨hAndType, hAndNumResults, hAndOperands, hAndProps⟩ := matchAnd_implies hAnd
  have hMIn : (ValuePtr.opResult mPtr).InBounds ctx.raw := hmIn
  have hAndOpIn : mPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hmIdx : mPtr.index < mPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hmEq : mPtr = mPtr.op.getResult 0 := by
    have hidx : mPtr.index = 0 := by omega
    cases mPtr; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx⟩
  have hVTypeEq : (ValuePtr.opResult mPtr).getType! ctx.raw
      = ((mPtr.op.getResult 0).get! ctx.raw).type := by rw [hmEq]; rfl
  have hAndVerified : mPtr.op.Verified ctx hAndOpIn := by grind
  obtain ⟨-, -, -, -, vIntTy, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_and hAndVerified hAndType
  have hResTyVal : ((mPtr.op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [← hVTypeEq]; exact hMType
  have hvEq : vIntTy = intType := by rw [hResType] at hResTyVal; simpa using hResTyVal
  subst vIntTy
  have hO0IdxEq : o0 = (mPtr.op.getOperands! ctx.raw)[0]! := by rw [hAndOperands]; rfl
  have hO1IdxEq : o1 = (mPtr.op.getOperands! ctx.raw)[1]! := by rw [hAndOperands]; rfl
  have hO0Op : mPtr.op.getOperand! ctx.raw 0 = o0 := by
    rw [hO0IdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hO1Op : mPtr.op.getOperand! ctx.raw 1 = o1 := by
    rw [hO1IdxEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hO0Type : (o0.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hO0Op, hOp0Type]
  have hO1Type : (o1.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hO1Op, hOp1Type]
  have hAndDefines : (ValuePtr.opResult mPtr).getDefiningOp! ctx.raw = some mPtr.op := by
    have hOwner := (ctx.wellFormed.operations mPtr.op hAndOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hAndSDom : mPtr.op.strictlyDominates op ctx := hSDom
  have hAndDomIp : mPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hAndPure : mPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_and hAndType
  obtain ⟨cfA, hInterpAnd⟩ := stateWf mPtr.op hAndOpIn hAndPure hAndDomIp
  obtain ⟨o0v, o1v, hO0Val, hO1Val, -, hMResVal, -⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .and)
      (srcFn := fun a b _ => Data.LLVM.Int.and a b)
      (props := mPtr.op.getProperties! ctx.raw (.llvm .and))
      hAndOpIn hAndType hAndNumResults hAndOperands rfl
      (by intro bw a b props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp'] at hh
          split at hh
          · exact absurd hh (by simp)
          · simp only [Data.LLVM.Int.cast_self, pure, Interp, Option.some.injEq, UBOr.ok.injEq] at hh
            grind)
      hInterpAnd hO0Type hO1Type
  exact ⟨o0v, o1v, hO0Val, hO1Val, by rw [hmEq]; exact hMResVal⟩

/-! ## Layer-2 matcher lemmas for the two `Option`-shaped orcb guards -/

theorem matchOrcbRight_implies {b m : ValuePtr} {y : Nat} {ctx : IRContext OpCode}
    {e : propertiesOf (.llvm .lshr)} (h : matchOrcbRight b m y ctx = some e) :
    (y = 0 ∧ b = m ∧ e.exact = false) ∨
    (y ≠ 0 ∧ ∃ bOp yShamt yc, getDefiningOp b ctx = some bOp ∧
      matchLshr bOp ctx = some (m, yShamt, e) ∧
      matchConstantIntVal yShamt ctx = some yc ∧ yc.value = (y : Int)) := by
  unfold matchOrcbRight at h
  split at h
  · rename_i hy0
    split at h
    · rename_i hbm
      refine Or.inl ⟨hy0, hbm, ?_⟩
      simp only [Option.some.injEq] at h
      subst h
      rfl
    · simp at h
  · rename_i hy
    refine Or.inr ⟨hy, ?_⟩
    cases hbOp : getDefiningOp b ctx with
    | none => simp [hbOp] at h
    | some bOp =>
      cases hL : matchLshr bOp ctx with
      | none => simp [hbOp, hL] at h
      | some triple =>
        obtain ⟨m', yShamt, lp⟩ := triple
        cases hyc : matchConstantIntVal yShamt ctx with
        | none => simp [hbOp, hL, hyc] at h
        | some yc =>
          simp only [hbOp, hL, hyc] at h
          split at h
          · rename_i hcond
            obtain ⟨hy1, rfl⟩ := hcond
            exact ⟨bOp, yShamt, yc, by grind, by grind, by grind, hy1⟩
          · simp at h

theorem matchOrcbMask_implies {mo0 mo1 : ValuePtr} {y : Nat} {ctx : IRContext OpCode}
    {z : ValuePtr} {attr : IntegerAttr} (h : matchOrcbMask mo0 mo1 y ctx = some (z, attr)) :
    BitVec.ofInt 64 attr.value = orcbMaskBV y ∧
    ((z = mo0 ∧ matchConstantIntVal mo1 ctx = some attr) ∨
     (z = mo1 ∧ matchConstantIntVal mo0 ctx = some attr)) := by
  unfold matchOrcbMask at h
  split at h
  · rename_i attr1 h1
    split at h
    · rename_i hm1
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hm1, Or.inl ⟨rfl, h1⟩⟩
    · split at h
      · rename_i attr0 h0
        split at h
        · rename_i hm0
          simp at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hm0, Or.inr ⟨rfl, h0⟩⟩
        · simp at h
      · simp at h
  · split at h
    · rename_i attr0 h0
      split at h
      · rename_i hm0
        simp at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨hm0, Or.inr ⟨rfl, h0⟩⟩
      · simp at h
    · simp at h

/-- The masked byte-indicator value: `0x0101…01 <<< Y`, whose only set bit in each byte is bit `Y`. -/
def orcbMask (Y : Nat) : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< Y

/-- The proof-side mask and the pattern-side mask (`RISCV64Sdag.orcbMaskBV`) agree. -/
theorem orcbMask_eq (y : Nat) : orcbMask y = orcbMaskBV y := rfl

/-- Core refinement: when `M = Z &&& (0x0101…01 <<< Y)` (each byte is `0` or `2^Y`), the LLVM idiom
    `sub (shl M (8-Y)) (lshr M Y)` computes exactly `riscv.orcb M` (`0xFF` per nonzero byte). Proved
    per `Y ∈ {0,…,7}` by `bv_decide`. -/
theorem orcb_isRefinedBy (Y : Nat) (hY : Y ≤ 7) (subNsw subNuw shlNsw shlNuw exact : Bool)
    {Z mt : Data.LLVM.Int 64}
    (h : Data.LLVM.Int.and Z (Data.LLVM.Int.val (orcbMask Y)) ⊒ mt) :
    Data.LLVM.Int.sub
      (Data.LLVM.Int.shl (Data.LLVM.Int.and Z (Data.LLVM.Int.val (orcbMask Y)))
        (Data.LLVM.Int.constant 64 ((8 - Y : Nat) : Int)) shlNsw shlNuw)
      (Data.LLVM.Int.lshr (Data.LLVM.Int.and Z (Data.LLVM.Int.val (orcbMask Y)))
        (Data.LLVM.Int.constant 64 (Y : Int)) exact) subNsw subNuw
      ⊒ RISCV.Reg.toInt (Data.RISCV.orcb (LLVM.Int.toReg mt)) 64 := by
  rcases Y with _|_|_|_|_|_|_|_|Y <;>
    first
      | (revert h; simp only [orcbMask, Data.LLVM.Int.constant]; veir_bv_decide)
      | exact absurd hY (by omega)


/-- `lshr x 0` is the identity. Lets the `Y = 0` case of `orcb_local` (whose right operand is `M`
    itself, with no `lshr`) reuse the *same* `orcb_isRefinedBy` instance as `Y > 0`, instead of
    needing a separate data lemma. -/
theorem lshr_constant_zero_64 (x : Data.LLVM.Int 64) (e : Bool) :
    Data.LLVM.Int.lshr x (Data.LLVM.Int.constant 64 0) e = x := by
  cases e <;> veir_bv_decide

/-- `orcb_local`'s soundness gate accepts the mask on *either* operand of the `and`, while
    `orcb_isRefinedBy` fixes it as the second; this commutes them. -/
theorem llvm_and_comm {w : Nat} (x y : Data.LLVM.Int w) :
    Data.LLVM.Int.and x y = Data.LLVM.Int.and y x := by
  cases x <;> cases y <;> simp [Data.LLVM.Int.and, Id.run, BitVec.and_comm]

/-- Bridge the matcher's `getDefiningOp` to the dominance API's `getDefiningOp!`, for a defining
    op with a single result. -/
theorem getDefiningOp!_of_getDefiningOp {ctx : WfIRContext OpCode} {v : ValuePtr}
    {o : OperationPtr} (hIn : v.InBounds ctx.raw) (h : getDefiningOp v ctx.raw = some o)
    (hNum : o.getNumResults! ctx.raw = 1) :
    v.getDefiningOp! ctx.raw = some o := by
  obtain ⟨p, rfl, rfl⟩ := getDefiningOp_implies h
  have hOpIn : p.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hIdx : p.index < p.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hidx0 : p.index = 0 := by omega
  have hEq : p = p.op.getResult 0 := by
    cases p; simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]; exact ⟨trivial, hidx0⟩
  have hOwner := (ctx.wellFormed.operations p.op hOpIn).result_owner 0 (by grind)
  grind [ValuePtr.getDefiningOp!]

set_option maxHeartbeats 1000000 in
/-- `matchConstantIntVal_getVar?_of_EquationLemmaAt`, generalized so the constant may be an operand
    of an intermediate op `midOp` that strictly dominates `op`, rather than of `op` itself.
    `orcb_local` needs this: the mask constant is an operand of the `and`, which is two levels
    below the matched `sub`. -/
theorem matchConstantIntVal_getVar?_of_strictlyDominates {ctx : WfIRContext OpCode}
    (ctxDom : ctx.Dom) (ctxVerif : ctx.Verified)
    {op : OperationPtr} (opInBounds : op.InBounds ctx.raw)
    {state : InterpreterState ctx}
    (stateWf : state.EquationLemmaAt (InsertPoint.before op) (by grind))
    {midOp : OperationPtr} {v : ValuePtr} {intAttr : IntegerAttr} {intType : IntegerType}
    (hMatch : matchConstantIntVal v ctx.raw = some intAttr)
    (hMidIn : midOp.InBounds ctx.raw)
    (hOperand : v ∈ midOp.getOperands! ctx.raw)
    (hMidSDom : midOp.strictlyDominates op ctx)
    (hVType : (v.getType! ctx.raw).val = Attribute.integerType intType) :
    state.variables.getVar? v = some (RuntimeValue.int intType.bitwidth
      (Data.LLVM.Int.constant intType.bitwidth intAttr.value)) := by
  obtain ⟨cstPtr, rfl, hCstOp⟩ := matchConstantIntVal_implies hMatch
  obtain ⟨hCstType, hCstProps⟩ := matchConstantIntOp_implies hCstOp
  have hCstIn : (ValuePtr.opResult cstPtr).InBounds ctx.raw := by grind
  have hCstOpIn : cstPtr.op.InBounds ctx.raw := by grind [OpResultPtr.InBounds]
  have hCstVerified : cstPtr.op.Verified ctx hCstOpIn := by grind
  obtain ⟨hCstNumResults, -, -, -⟩ :=
    OperationPtr.Verified.llvm_mlir__constant hCstVerified hCstType
  have hCstIdx : cstPtr.index < cstPtr.op.getNumResults! ctx.raw := by
    grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
  have hCstEq : cstPtr = cstPtr.op.getResult 0 := by
    have hidx : cstPtr.index = 0 := by omega
    cases cstPtr
    simp only [OperationPtr.getResult, OpResultPtr.mk.injEq]
    exact ⟨trivial, hidx⟩
  have hCstResType : ((cstPtr.op.getResult 0).get! ctx.raw).type
      = ⟨.integerType intType, by grind⟩ := by
    have heq : ((ValuePtr.opResult cstPtr).getType! ctx.raw)
        = ((cstPtr.op.getResult 0).get! ctx.raw).type := by rw [hCstEq]; rfl
    apply Subtype.ext
    rw [← heq]; exact hVType
  have hCstDefines : (ValuePtr.opResult cstPtr).getDefiningOp! ctx.raw = some cstPtr.op := by
    have hOwner := (ctx.wellFormed.operations cstPtr.op hCstOpIn).result_owner 0 (by grind)
    grind [ValuePtr.getDefiningOp!]
  have hCstSDomMid : cstPtr.op.strictlyDominates midOp ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom
      hCstDefines hOperand
  have hCstSDom : cstPtr.op.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hCstSDomMid hMidSDom
  have hCstDomIp : cstPtr.op.dominatesIp (InsertPoint.before op) ctx := by grind
  have hCstPure : cstPtr.op.Pure ctx.raw := OperationPtr.Pure.llvm_mlir__constant hCstType
  obtain ⟨cfC, hInterpCst⟩ := stateWf cstPtr.op hCstOpIn hCstPure hCstDomIp
  have hCstResVal :=
    constantOp_interpretOp_unfold hCstOpIn hCstType hCstNumResults hCstProps hCstResType
      hInterpCst
  rw [hCstEq]; exact hCstResVal

/-! ## The structural correctness proof -/

set_option maxHeartbeats 4000000 in
/-- `orcb_local` preserves semantics: `sub (shl M (8-Y)) (lshr M Y)` lowered to
    `riscv.orcb M` refines the source, given the soundness gate `M = and Z (0x0101…01 <<< Y)`.
    The `Y = 0` case (whose right operand is `M` itself) collapses onto the same
    `orcb_isRefinedBy` instance via `lshr_constant_zero_64`, so both cases share one tail. -/
theorem orcb_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps orcb_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges orcb_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds orcb_local}
    {h₄ : LocalRewritePattern.ReturnValues orcb_local} :
    LocalRewritePattern.PreservesSemantics orcb_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, orcb_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp [Option.bind_eq_bind, pure, Option.bind_eq_bind] at hpattern
  have hMatchSome : (matchSub op ctx.raw).isSome := by
    cases hM : matchSub op ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨a, b, subProps⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  obtain ⟨hOpType, hNumResults, hOperands, hSubProps⟩ := matchSub_implies hMatch
  -- Establish this before peeling: with the emit chain in `hpattern`, `grind` blows up.
  have hResultsEq : ∀ (hin : op.InBounds ctx.raw),
      op.getResults ctx.raw hin = #[ValuePtr.opResult (op.getResult 0)] := by
    intro hin; grind
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hNSucc, hNReg, intType, hResType, hOp0Type, hOp1Type⟩ :=
    OperationPtr.Verified.llvm_sub opVerif hOpType
  have hAEq : a = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hBEq : b = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = a := by
    rw [hAEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = b := by
    rw [hBEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hAType : (a.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand0, hOp0Type]
  have hBType : (b.getType! ctx.raw).val = Attribute.integerType intType := by
    rw [← hOperand1, hOp1Type]
  have hResTypeVal : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType intType := by
    rw [hResType]
  rw [hResTypeVal] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isFalse hne => simp at hpattern
  rename_i hW64
  have hDefASome : (getDefiningOp a ctx.raw).isSome := by
    cases hM : getDefiningOp a ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨aOp, hDefA⟩ := Option.isSome_iff_exists.mp hDefASome
  rw [hDefA] at hpattern
  simp only [] at hpattern
  have hShlSome : (matchShl aOp ctx.raw).isSome := by
    cases hM : matchShl aOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨m, shamt, shlProps⟩, hShl⟩ := Option.isSome_iff_exists.mp hShlSome
  rw [hShl] at hpattern
  simp only [] at hpattern
  have hShcSome : (matchConstantIntVal shamt ctx.raw).isSome := by
    cases hM : matchConstantIntVal shamt ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨shc, hShcMatch⟩ := Option.isSome_iff_exists.mp hShcSome
  rw [hShcMatch] at hpattern
  simp only [] at hpattern
  split at hpattern
  case isTrue hrange => simp at hpattern
  rename_i hRange
  have hShcLo : 1 ≤ shc.value := by simp at hRange; omega
  have hShcHi : shc.value ≤ 8 := by simp at hRange; omega
  obtain ⟨hShlOpType, hShlNumResults, hShlOperands, hShlPropsEq⟩ := matchShl_implies hShl
  -- Source interpretation of the matched `sub`.
  obtain ⟨av, bv, haVal, hbVal, hMem, hRes, hCf⟩ :=
    matchBinaryOp_interpretOp_unfold (srcOp := .sub)
      (srcFn := fun x y p => Data.LLVM.Int.sub x y p.nsw p.nuw)
      (props := op.getProperties! ctx.raw (.llvm .sub))
      opInBounds hOpType hNumResults hOperands rfl
      (by intro bw x y props resultTypes blockOperands mem res hh
          simp only [Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp] at hh
          grind)
      hinterp hAType hBType
  subst hCf
  -- `a`'s value, via the `shl` graph lemma.
  obtain ⟨mv, hmVal, haShl, hmType, hmDom, hmIn, hmNotRes⟩ :=
    shl_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefA hShl hShcMatch
      (by rw [hOperands]; simp) hAType
  obtain rfl : av = Data.LLVM.Int.shl mv
      (Data.LLVM.Int.constant intType.bitwidth shc.value) shlProps.nsw shlProps.nuw := by
    have := haVal.symm.trans haShl; simpa using this
  -- Collapse the bitwidth to the literal 64.
  obtain ⟨bw⟩ := intType
  simp only at hW64 hmType hmVal hbVal hRes hAType hBType hResTypeVal ⊢
  subst hW64
  -- The right-operand guard is now `Option`-shaped and peels with a plain `rw`.
  have hRightSome : (matchOrcbRight b m ((8 - shc.value).toNat) ctx.raw).isSome := by
    cases hM : matchOrcbRight b m ((8 - shc.value).toNat) ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨lshrProps, hRight⟩ := Option.isSome_iff_exists.mp hRightSome
  rw [hRight] at hpattern
  simp only [] at hpattern
  -- Soundness gate.
  have hDefMSome : (getDefiningOp m ctx.raw).isSome := by
    cases hM : getDefiningOp m ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨mOp, hDefM⟩ := Option.isSome_iff_exists.mp hDefMSome
  rw [hDefM] at hpattern
  simp only [] at hpattern
  have hAndSome : (matchAnd mOp ctx.raw).isSome := by
    cases hM : matchAnd mOp ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨mo0, mo1, andProps⟩, hAnd⟩ := Option.isSome_iff_exists.mp hAndSome
  rw [hAnd] at hpattern
  simp only [] at hpattern
  have hMaskSome : (matchOrcbMask mo0 mo1 ((8 - shc.value).toNat) ctx.raw).isSome := by
    cases hM : matchOrcbMask mo0 mo1 ((8 - shc.value).toNat) ctx.raw with
    | some z => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨zVal, maskAttr⟩, hMask⟩ := Option.isSome_iff_exists.mp hMaskSome
  rw [hMask] at hpattern
  simp only [] at hpattern
  -- `b`'s value: `lshr m Y` (the `Y = 0` case collapses onto it via `lshr_constant_zero_64`).
  have hY7 : (8 - shc.value).toNat ≤ 7 := by omega
  obtain ⟨e, hbvEq⟩ : ∃ e : Bool, bv = Data.LLVM.Int.lshr mv
      (Data.LLVM.Int.constant 64 (((8 - shc.value).toNat : Nat) : Int)) e := by
    rcases matchOrcbRight_implies hRight with ⟨hy0, hbm, hex⟩ |
      ⟨hy, bOp, yShamt, yc, hDefB, hLshr, hYc, hYcVal⟩
    · refine ⟨false, ?_⟩
      have hbvm : bv = mv := by
        have := (hbm ▸ hbVal).symm.trans hmVal; simpa using this
      have hz : (((8 - shc.value).toNat : Nat) : Int) = 0 := by omega
      simp only [hbvm, hz]
      exact (lshr_constant_zero_64 mv false).symm
    · refine ⟨lshrProps.exact, ?_⟩
      obtain ⟨mv', hmVal', hbLshr, -, -, -, -⟩ :=
        lshrConst_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefB hLshr hYc
          (by rw [hOperands]; simp) hBType
      have hmv' : mv' = mv := by
        have := hmVal'.symm.trans hmVal; simpa using this
      rw [hmv'] at hbLshr
      have hb : bv = Data.LLVM.Int.lshr mv
          (Data.LLVM.Int.constant 64 yc.value) lshrProps.exact := by
        have := hbVal.symm.trans hbLshr; simpa using this
      rw [hb, hYcVal]
  subst hbvEq
  -- Dominance chain `mOp ⊐ aOp ⊐ op`.
  obtain ⟨hShlOpType', hShlNumResults', hShlOperands', -⟩ := matchShl_implies hShl
  obtain ⟨hAndOpType, hAndNumResults, hAndOperands, hAndPropsEq⟩ := matchAnd_implies hAnd
  have hAIn : a.InBounds ctx.raw := by grind
  have hADefines := getDefiningOp!_of_getDefiningOp hAIn hDefA hShlNumResults'
  have hAOpSDom : aOp.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hADefines
      (by rw [hOperands]; simp)
  have hMDefines := getDefiningOp!_of_getDefiningOp hmIn hDefM hAndNumResults
  have hMOpSDomA : mOp.strictlyDominates aOp ctx :=
    OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands! ctxDom hMDefines
      (by rw [hShlOperands']; simp)
  have hMOpSDom : mOp.strictlyDominates op ctx :=
    OperationPtr.strictlyDominates_trans hMOpSDomA hAOpSDom
  have hMOpIn : mOp.InBounds ctx.raw := by
    obtain ⟨mPtr, hmp, hmo⟩ := getDefiningOp_implies hDefM
    subst hmo; rw [hmp] at hmIn; grind [OpResultPtr.InBounds]
  -- `m = and o0v o1v`.
  obtain ⟨o0v, o1v, hO0Val, hO1Val, hmAnd⟩ :=
    and_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf hDefM hAnd hMOpSDom hmIn
      hmType
  have hmvAnd : mv = Data.LLVM.Int.and o0v o1v := by
    have := hmVal.symm.trans hmAnd; simpa using this
  -- Operand types of the `and`.
  have hAndVerified : mOp.Verified ctx hMOpIn := by grind
  obtain ⟨-, -, -, -, andIntTy, hAndResType, hAndOp0Type, hAndOp1Type⟩ :=
    OperationPtr.Verified.llvm_and hAndVerified hAndOpType
  have hmResTy : ((mOp.getResult 0).get! ctx.raw).type.val = Attribute.integerType andIntTy := by
    rw [hAndResType]
  have hmIsRes : m = ValuePtr.opResult (mOp.getResult 0) := by
    obtain ⟨mPtr, hmp, hmo⟩ := getDefiningOp_implies hDefM
    subst hmo
    have hIdx : mPtr.index < mPtr.op.getNumResults! ctx.raw := by
      rw [hmp] at hmIn; grind [OpResultPtr.inBounds_OperationPtr_getNumResults!]
    have hidx0 : mPtr.index = 0 := by omega
    rw [hmp]; cases mPtr
    simp only [OperationPtr.getResult] at *
    grind
  have hAndIntTy : andIntTy = ⟨64⟩ := by
    rw [hmIsRes] at hmType
    have : (ValuePtr.opResult (mOp.getResult 0)).getType! ctx.raw
        = ((mOp.getResult 0).get! ctx.raw).type := rfl
    rw [this, hmResTy] at hmType; grind
  subst hAndIntTy
  have hO0Eq : mo0 = (mOp.getOperands! ctx.raw)[0]! := by rw [hAndOperands]; rfl
  have hO1Eq : mo1 = (mOp.getOperands! ctx.raw)[1]! := by rw [hAndOperands]; rfl
  have hO0Op : mOp.getOperand! ctx.raw 0 = mo0 := by
    rw [hO0Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hO1Op : mOp.getOperand! ctx.raw 1 = mo1 := by
    rw [hO1Eq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hO0Type : (mo0.getType! ctx.raw).val = Attribute.integerType ⟨64⟩ := by
    rw [← hO0Op, hAndOp0Type]
  have hO1Type : (mo1.getType! ctx.raw).val = Attribute.integerType ⟨64⟩ := by
    rw [← hO1Op, hAndOp1Type]
  -- Pin the mask operand and rewrite `m` as `and Z (val mask)`.
  obtain ⟨hMaskVal, hSide⟩ := matchOrcbMask_implies hMask
  have hMaskConst : ∀ (v : ValuePtr) (attr : IntegerAttr),
      matchConstantIntVal v ctx.raw = some attr → v ∈ mOp.getOperands! ctx.raw →
      (v.getType! ctx.raw).val = Attribute.integerType ⟨64⟩ →
      state.variables.getVar? v = some (RuntimeValue.int 64
        (Data.LLVM.Int.constant 64 attr.value)) := by
    intro v attr hv hvin hvty
    exact matchConstantIntVal_getVar?_of_strictlyDominates ctxDom ctxVerif opInBounds stateWf
      hv hMOpIn hvin hMOpSDom hvty
  have hMaskIsVal : Data.LLVM.Int.constant 64 maskAttr.value
      = Data.LLVM.Int.val (orcbMask ((8 - shc.value).toNat)) := by
    simp only [Data.LLVM.Int.constant, orcbMask_eq, hMaskVal]
  obtain ⟨Z, hmvZ⟩ : ∃ Z, mv = Data.LLVM.Int.and Z
      (Data.LLVM.Int.val (orcbMask ((8 - shc.value).toNat))) := by
    rcases hSide with ⟨rfl, hc1⟩ | ⟨rfl, hc0⟩
    · refine ⟨o0v, ?_⟩
      have := hMaskConst mo1 maskAttr hc1 (by rw [hAndOperands]; simp) hO1Type
      have ho1 : o1v = Data.LLVM.Int.constant 64 maskAttr.value := by
        have := hO1Val.symm.trans this; simpa using this
      rw [hmvAnd, ho1, hMaskIsVal]
    · refine ⟨o1v, ?_⟩
      have := hMaskConst mo0 maskAttr hc0 (by rw [hAndOperands]; simp) hO0Type
      have ho0 : o0v = Data.LLVM.Int.constant 64 maskAttr.value := by
        have := hO0Val.symm.trans this; simpa using this
      rw [hmvAnd, ho0, hMaskIsVal, llvm_and_comm]
  -- Source value.
  rw [hResultsEq] at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Shrink the context before peeling: `grind` inside the `peel*` macros is non-monotonic in
  -- context size (see `ProofStrategy.md`), and these facts have all been consumed.
  clear hRight hMask hSide hMaskConst hMaskIsVal hO0Val hO1Val hmAnd hmvAnd
  clear hAndResType hAndOp0Type hAndOp1Type hO0Eq hO1Eq hO0Op hO1Op hO0Type hO1Type hmResTy hmIsRes
  clear hAndOperands hAndOpType hAndNumResults hAndPropsEq hMDefines hMOpSDomA hMOpSDom
  clear hADefines hAOpSDom hAIn hShlOpType' hShlNumResults' hShlOperands'
  clear hMOpIn hDefM hAnd hAndVerified hDefA hShl hShcMatch hMatchSome hRes hbVal haVal
  -- Peel the three creations.
  peelCastToRegLocal hpattern ctx₁ mCastOp hMCast hmDom hmDom₁
  peelOpCreation! hpattern ctx₂ orcbOp hOrcb hmDom₁ hmDom₂
  peelReplaceWithRegLocal hpattern ctx₃ castBackOp hCastBack hmDom₂ hmDom₃
  cleanupHpattern hpattern
  obtain ⟨mt, hMVal', hmtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom hmIn hmVal
      hmDom hmDom₃ hmNotRes
  have hMCastType : mCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hOrcbType : orcbOp.getOpType! ctx₃.raw = .riscv .orcb := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hMCastOperands : mCastOp.getOperands! ctx₃.raw = #[m] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hMCast (operation := mCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hOrcb (operation := mCastOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := mCastOp)]
  have hOrcbOperands :
      orcbOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (mCastOp.getResult 0)] := by
    grind [OperationPtr.getOperands!_WfRewriter_createOp hOrcb (operation := orcbOp),
      OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := orcbOp)]
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (orcbOp.getResult 0)] := by grind
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType { bitwidth := 64 }, by grind⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hOrcb
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hMCast
          (value := ValuePtr.opResult (op.getResult 0))]
    rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
    rw [h1]; exact Subtype.ext hResTypeVal
  have hMCastResTypes :
      mCastOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hMCast (operation := mCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hOrcb (operation := mCastOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := mCastOp)]
  have hOrcbResTypes :
      orcbOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hOrcb (operation := orcbOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := orcbOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType { bitwidth := 64 }, by grind⟩] := by grind
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hMCastType hMCastOperands hMCastResTypes hMVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_forward (state := s₁) (inBounds := by grind)
      (f := Data.RISCV.orcb) (fun _ _ _ _ => rfl)
      hOrcbType hOrcbOperands hOrcbResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  refine ⟨#[RuntimeValue.int 64
      (RISCV.Reg.toInt (Data.RISCV.orcb (LLVM.Int.toReg mt)) 64)],
    by simp [hRes₃, Option.bind, Option.map], ?_⟩
  refine RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, ?_⟩
  -- Discharge with the core data lemma.
  have hZref : Data.LLVM.Int.and Z
      (Data.LLVM.Int.val (orcbMask ((8 - shc.value).toNat))) ⊒ mt := by
    rw [← hmvZ]; exact hmtRef
  have hlem := orcb_isRefinedBy ((8 - shc.value).toNat) hY7
    subProps.nsw subProps.nuw shlProps.nsw shlProps.nuw e hZref
  have hshl : ((8 - (8 - shc.value).toNat : Nat) : Int) = shc.value := by omega
  rw [hshl] at hlem
  rw [hmvZ, ← hSubProps]
  simpa using hlem

end Veir
