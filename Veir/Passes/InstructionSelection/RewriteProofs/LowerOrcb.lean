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

/-- The masked byte-indicator value: `0x0101…01 <<< Y`, whose only set bit in each byte is bit `Y`. -/
def orcbMask (Y : Nat) : BitVec 64 := BitVec.ofNat 64 0x0101010101010101 <<< Y

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

/-
The structural correctness proof `orcb_local_preservesSemantics` is still a work in progress.
Everything it needs is now in place above, and all of it builds and is axiom-clean:

  * the core bitvector identity and the `orcb_isRefinedBy` data lemma (all `Y ∈ {0,…,7}` and all
    shift/sub flag combinations);
  * `shl_getVar?` / `and_getVar?` — the DAG graph lemmas for the matched `shl` and `and`;
  * `matchConstantIntVal_getVar?_of_strictlyDominates` — the constant graph lemma generalized to a
    constant that is an operand of an op *two levels* below the matched `sub` (the mask);
  * `getDefiningOp!_of_getDefiningOp` — needed to build the dominance chain `andOp ⊐ shlOp ⊐ op`
    that `and_getVar?` and the constant lemma take as input;
  * `lshr_constant_zero_64`, which collapses the `Y = 0` case (whose right operand is `M` itself,
    with no `lshr`) onto the same `orcb_isRefinedBy` instance as `Y > 0`, so the two cases share
    one data lemma rather than needing two;
  * `llvm_and_comm`, for the soundness gate accepting the mask on either `and` operand.

What remains is the final assembly, following the `bexti_local_preservesSemantics` template
(`LowerBexti.lean`) — the same three-op `castToRegLocal → orcb → replaceWithRegLocal` emit chain:

  1. Peel `matchSub`, the result-type/width guards, `getDefiningOp a`, `matchShl`,
    `matchConstantIntVal shamt`, and the `1 ≤ shc.value ≤ 8` range guard. (Drafted and building.)
  2. Peel the `rightMatches` guard. After the initial `simp … at hpattern` this is an *`ite` whose
    condition is itself an `ite`*, so a bare `split at hpattern` splits the inner condition
    (`8 - shc.value ≤ 0`), not the outer one. Trying to discharge the outer guard without
    branching does not work: both `rw [if_pos …]` and `simp only [if_pos …]` fail to fire against
    a hand-written copy of the condition, because the elaborated `Decidable` instance does not
    match. So split on the inner condition and handle the two cases. In the resulting inner
    `split`, `isTrue` is the *bail* case (`¬ b = m`), not the continuing one.
  2a. In the `Y > 0` case, peeling `matchLshr` out of `hpattern` is the open problem:
    `rw [hLshr] at hpattern` fails with `motive is not type correct` and `simp only [hLshr] at
    hpattern` makes no progress. The match on `matchLshr bOp ctx.raw` sits inside a *`Bool`-valued*
    `match` (`| none => false | some (m', …) => … decide (m' = m)`) under `if _ = false`, unlike the
    `Option`-valued matches elsewhere in the pattern, which `rw` peels fine. The `Y = 0` case peels
    and derives its `bv` fact without trouble.
  3. In the `Y = 0` case the guard yields `b = m`; rewrite `b`'s value with
    `lshr_constant_zero_64`. In the `Y > 0` case, recover `b`'s value with
    `lshrConst_getVar?_of_EquationLemmaAt` (`LowerBexti.lean`). Both then establish
    `∃ e, bv = lshr mv (constant 64 Y) e`, after which the tail is shared: `obtain ⟨e, rfl⟩`
    substitutes `bv` and keeps `mv`. (Deriving these as an existential, rather than `obtain rfl`
    on `bv = mv`, matters: the latter eliminates `mv`, which the rest of the proof needs.)
  4. Peel the soundness gate (`getDefiningOp m`, `matchAnd`, the mask check), pin the mask operand
    with `matchConstantIntVal_getVar?_of_strictlyDominates`, and commute it into second position
    with `llvm_and_comm` when it matched on the left.
  5. Peel the three creations with `peelCastToRegLocal` / `peelOpCreation!` /
    `peelReplaceWithRegLocal`, discharge the `getOpType!`/`getOperands!`/`getResultTypes!`
    transports (seed them explicitly per creation, as in `LowerBexti.lean`), replay the chain with
    `interpretOp_castToReg_forward` / `interpretOp_riscv_unaryReg_forward` /
    `interpretOp_castBack_forward`, and close with `orcb_isRefinedBy Y`.
-/

end Veir
