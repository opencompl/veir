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
import Veir.Passes.InstructionSelection.RISCV64Sdag
import Veir.Passes.InstructionSelection.RewriteProofs.CommonMatchEqns
import Veir.Passes.InstructionSelection.RewriteProofs.CommonTactics
import Veir.Passes.InstructionSelection.RewriteProofs.CommonBaseLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.CommonForwardInterpret
import Veir.Passes.InstructionSelection.RewriteProofs.CommonGraphLemmas
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelect
-- Imported for their pre-generated match-congruence auxiliaries (`lowerBinopNotLocal.match_1.…`),
-- which our `grind`/`split` calls share; without this the aggregator hits a duplicate-generation
-- clash (`LowerSelectBinopImm` bakes the single shared copy, as `LowerSelectSingleBit` also relies
-- on; see `CommonMatchEqns` for the general pattern).
import Veir.Passes.InstructionSelection.RewriteProofs.LowerRoriw
import Veir.Passes.InstructionSelection.RewriteProofs.LowerSelectBinopImm

namespace Veir

/-!
## Correctness of `slti_local`

`slti_local` lowers an `llvm.icmp x (const)` whose right operand is a constant fitting a signed
12-bit field directly to the immediate comparison instructions `slti`/`sltiu` (`PatGprSimm12`),
inverting the sense with `xori _ 1` for the `≥` predicates and using `x ≤ C == x < C+1` for the
`≤` predicates:

    slt  x C  ->       slti  x C
    ult  x C  ->       sltiu x C
    sge  x C  -> xori (slti  x C)      1
    uge  x C  -> xori (sltiu x C)      1
    sle  x C  ->       slti  x (C+1)
    ule  x C  ->       sltiu x (C+1)              (requires C ≠ -1)

Structurally this is `selectBinopImmLocal`'s `castToReg → imm-op → castBack` chain, but the source
op is `llvm.icmp` — whose operands are `i64` while its result is `i1` — so it is handled by the
bespoke `matchIcmp_interpretOp_unfold` (a mixed-width analogue of `matchBinaryOp_interpretOp_unfold`)
and a fresh `Verified.llvm_icmp` structural bundle. The `≥` predicates additionally wrap the
comparison in an `xori _ 1`, giving a four-op chain.
-/

/-! ### Forward unfolding of an `llvm.icmp` interpretation -/

set_option maxHeartbeats 800000 in
/-- Interpreting a matched `llvm.icmp` whose two operands have integer type `intType` reads the
    operands' `i{bw}` values `x`/`y` and stores `icmp x y props.predicate : i1` in the result
    variable, leaving memory and control flow untouched. The mixed-width analogue of
    `matchBinaryOp_interpretOp_unfold`. -/
theorem matchIcmp_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {lhs rhs : ValuePtr} {props : propertiesOf (.llvm .icmp)} {intType}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .icmp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[lhs, rhs])
    (hProps : props = op.getProperties! ctx.raw (.llvm .icmp))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf)))
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType)
    (hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType) :
    ∃ (x y : Data.LLVM.Int intType.bitwidth),
      state.variables.getVar? lhs = some (RuntimeValue.int intType.bitwidth x) ∧
      state.variables.getVar? rhs = some (RuntimeValue.int intType.bitwidth y) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int 1 (Data.LLVM.Int.icmp x y props.predicate)) ∧
      cf = none := by
  have hNumOperands : op.getNumOperands! ctx.raw = 2 := by
    simp [← OperationPtr.getOperands!.size_eq_getNumOperands!, hOperands]
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  obtain ⟨operandValues, _, _, _, hOperandValues, _⟩ := interpretOp_some_iff.mp hinterp
  simp only [VariableState.getOperandValues] at hOperandValues
  have hsize0 : 0 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  have hsize1 : 1 < (op.getOperands! ctx.raw).size := by
    rw [OperationPtr.getOperands!.size_eq_getNumOperands!]; omega
  obtain ⟨lval, hlval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 0 hsize0
  obtain ⟨rval, hrval⟩ :=
    Array.exists_mapM_option_eq_some_iff.mp ⟨operandValues, hOperandValues⟩ 1 hsize1
  have hlGetVar : state.variables.getVar? lhs = some lval := by
    rw [hLhsEq, show (op.getOperands! ctx.raw)[0]! = (op.getOperands! ctx.raw)[0] from by grind]
    exact hlval
  have hrGetVar : state.variables.getVar? rhs = some rval := by
    rw [hRhsEq, show (op.getOperands! ctx.raw)[1]! = (op.getOperands! ctx.raw)[1] from by grind]
    exact hrval
  have hlconf := VariableState.getVar?_conforms hlGetVar
  rw [show lhs.getType! ctx.raw = ⟨.integerType intType, hLhsType ▸ (lhs.getType! ctx.raw).2⟩
        from Subtype.ext hLhsType] at hlconf
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType hlconf
  have hrconf := VariableState.getVar?_conforms hrGetVar
  rw [show rhs.getType! ctx.raw = ⟨.integerType intType, hRhsType ▸ (rhs.getType! ctx.raw).2⟩
        from Subtype.ext hRhsType] at hrconf
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType hrconf
  refine ⟨x, y, hlGetVar, hrGetVar, ?_⟩
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int intType.bitwidth x, RuntimeValue.int intType.bitwidth y] := by
    rw [VariableState.getOperandValues_eq_some_iff]
    refine ⟨by simp [hNumOperands], fun i hi => ?_⟩
    rw [hNumOperands] at hi
    match i, hi with
    | 0, _ => simpa [hOperand0] using hlGetVar
    | 1, _ => simpa [hOperand1] using hrGetVar
  rw [interpretOp_some_iff] at hinterp
  obtain ⟨operandValues', resValues, mem', varState', hOV, hInterp', hSet, hNew⟩ := hinterp
  rw [hOpVals, Option.some.injEq] at hOV
  subst hOV
  simp only [OperationPtr.interpret] at hInterp'
  rw [hOpType] at hInterp'
  simp only [← hProps, interpretOp', Llvm.interpretOp', Data.LLVM.Int.cast_self, pure, Interp]
    at hInterp'
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int 1 (Data.LLVM.Int.icmp x y props.predicate)] ∧
      mem' = state.memory ∧ cf = none := by grind
  subst hNew
  refine ⟨rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

/-! ### Data-level refinement lemmas

Each relates the source comparison `icmp x (const 64 c) pred` to the emitted register value. They
factor through `icmp_mono` (to move from the source operand `x` to its refinement `xt`) and the
pure immediate-comparison refinements `icmp_refinement_*_imm` in `InstructionSelection.Proofs`. The
matched LLVM constant carries the full-width value `c`, whereas the emitted instruction sign-extends
its 12-bit immediate, so `signExtend_ofInt_12_64` bridges the two encodings (as in
`selectBinopImmLocal`). -/

/-- `slti x C` computes `x < C` directly (`PatGprSimm12<setlt, SLTI>`), immediate form. -/
theorem icmp_refinement_slt_imm {x : Data.LLVM.Int 64} (imm : BitVec 12) :
    (Data.LLVM.Int.icmp x (Data.LLVM.Int.val (imm.signExtend 64)) Data.LLVM.IntPred.slt) ⊒
      (RISCV.Reg.toInt (Data.RISCV.slti imm (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/-- `sltiu x C` computes `x <u C` directly (`PatGprSimm12<setult, SLTIU>`), immediate form. -/
theorem icmp_refinement_ult_imm {x : Data.LLVM.Int 64} (imm : BitVec 12) :
    (Data.LLVM.Int.icmp x (Data.LLVM.Int.val (imm.signExtend 64)) Data.LLVM.IntPred.ult) ⊒
      (RISCV.Reg.toInt (Data.RISCV.sltiu imm (LLVM.Int.toReg x)) 1) := by
  veir_bv_decide

/-- Bridge the matched constant `constant 64 c` into the sign-extended 12-bit encoding. -/
private theorem constant_eq_val_signExtend {c : Int} (hlo : -2048 ≤ c) (hhi : c ≤ 2047) :
    Data.LLVM.Int.constant 64 c = Data.LLVM.Int.val ((BitVec.ofInt 12 c).signExtend 64) := by
  rw [Data.LLVM.Int.constant, signExtend_ofInt_12_64 _ hlo hhi]

theorem icmp_slt_isRefinedBy_toInt_slti {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) Data.LLVM.IntPred.slt
      ⊒ RISCV.Reg.toInt (Data.RISCV.slti (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 1 :=
  isRefinedBy_trans
    (Data.LLVM.Int.icmp_mono x (Data.LLVM.Int.constant 64 c) xt (Data.LLVM.Int.constant 64 c)
      Data.LLVM.IntPred.slt h (isRefinedBy_refl _))
    (by rw [constant_eq_val_signExtend hlo hhi]; exact icmp_refinement_slt_imm (BitVec.ofInt 12 c))

theorem icmp_ult_isRefinedBy_toInt_sltiu {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) Data.LLVM.IntPred.ult
      ⊒ RISCV.Reg.toInt (Data.RISCV.sltiu (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 1 :=
  isRefinedBy_trans
    (Data.LLVM.Int.icmp_mono x (Data.LLVM.Int.constant 64 c) xt (Data.LLVM.Int.constant 64 c)
      Data.LLVM.IntPred.ult h (isRefinedBy_refl _))
    (by rw [constant_eq_val_signExtend hlo hhi]; exact icmp_refinement_ult_imm (BitVec.ofInt 12 c))

theorem icmp_sge_isRefinedBy_toInt_slti {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) Data.LLVM.IntPred.sge
      ⊒ RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 1)
          (Data.RISCV.slti (BitVec.ofInt 12 c) (LLVM.Int.toReg xt))) 1 :=
  isRefinedBy_trans
    (Data.LLVM.Int.icmp_mono x (Data.LLVM.Int.constant 64 c) xt (Data.LLVM.Int.constant 64 c)
      Data.LLVM.IntPred.sge h (isRefinedBy_refl _))
    (by rw [constant_eq_val_signExtend hlo hhi]
        exact Data.RISCV.icmp_refinement_sge_imm (BitVec.ofInt 12 c))

theorem icmp_uge_isRefinedBy_toInt_sltiu {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) Data.LLVM.IntPred.uge
      ⊒ RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 1)
          (Data.RISCV.sltiu (BitVec.ofInt 12 c) (LLVM.Int.toReg xt))) 1 :=
  isRefinedBy_trans
    (Data.LLVM.Int.icmp_mono x (Data.LLVM.Int.constant 64 c) xt (Data.LLVM.Int.constant 64 c)
      Data.LLVM.IntPred.uge h (isRefinedBy_refl _))
    (by rw [constant_eq_val_signExtend hlo hhi]
        exact Data.RISCV.icmp_refinement_uge_imm (BitVec.ofInt 12 c))

/-- Bridge `constant 64 c` into `sext(ofInt 12 (c+1)) - 1` for the off-by-one `≤` forms. -/
private theorem constant_eq_val_signExtend_pred {c : Int}
    (hlo : -2048 ≤ c + 1) (hhi : c + 1 ≤ 2047) :
    Data.LLVM.Int.constant 64 c
      = Data.LLVM.Int.val ((BitVec.ofInt 12 (c + 1)).signExtend 64 - 1) := by
  rw [Data.LLVM.Int.constant, signExtend_ofInt_12_64 _ hlo hhi]
  congr 1
  bv_omega

/-- `BitVec.ofInt 12 (c+1)` is nonzero when `c ≠ -1` and `c+1` fits a signed 12-bit field. -/
private theorem ofInt_12_succ_ne_zero {c : Int} (hlo : -2048 ≤ c + 1) (hhi : c + 1 ≤ 2047)
    (hc : c ≠ -1) : BitVec.ofInt 12 (c + 1) ≠ 0 := by
  intro heq
  bv_omega

theorem icmp_sle_isRefinedBy_toInt_slti {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c + 1) (hhi : c + 1 ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) Data.LLVM.IntPred.sle
      ⊒ RISCV.Reg.toInt (Data.RISCV.slti (BitVec.ofInt 12 (c + 1)) (LLVM.Int.toReg xt)) 1 :=
  isRefinedBy_trans
    (Data.LLVM.Int.icmp_mono x (Data.LLVM.Int.constant 64 c) xt (Data.LLVM.Int.constant 64 c)
      Data.LLVM.IntPred.sle h (isRefinedBy_refl _))
    (by rw [constant_eq_val_signExtend_pred hlo hhi]
        exact Data.RISCV.icmp_refinement_sle_imm (BitVec.ofInt 12 (c + 1)))

theorem icmp_ule_isRefinedBy_toInt_sltiu {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c + 1) (hhi : c + 1 ≤ 2047) (hc : c ≠ -1) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) Data.LLVM.IntPred.ule
      ⊒ RISCV.Reg.toInt (Data.RISCV.sltiu (BitVec.ofInt 12 (c + 1)) (LLVM.Int.toReg xt)) 1 :=
  isRefinedBy_trans
    (Data.LLVM.Int.icmp_mono x (Data.LLVM.Int.constant 64 c) xt (Data.LLVM.Int.constant 64 c)
      Data.LLVM.IntPred.ule h (isRefinedBy_refl _))
    (by rw [constant_eq_val_signExtend_pred hlo hhi]
        exact Data.RISCV.icmp_refinement_ule_imm (BitVec.ofInt 12 (c + 1))
          (ofInt_12_succ_ne_zero hlo hhi hc))

/-! ### Shared correctness of `sltiEmitLocal`

The `castToReg (value operand) → dst (imm) → [xori _ 1] → castBack` chain refines the source
`icmp x (const c) pred : i1`, given the source-side facts established by `slti_local`'s shared
prefix and a per-predicate data-level refinement `hData`. Two variants: `noWrap` (three-op chain,
for `slt`/`ult`/`sle`/`ule`) and `wrap` (four-op chain, appending `xori _ 1`, for `sge`/`uge`). -/

set_option maxHeartbeats 1600000 in
theorem sltiEmitLocal_noWrap_sound {ctx : WfIRContext OpCode} (_ctxDom : ctx.Dom)
    {op : OperationPtr} {lhs : ValuePtr} {opInBounds : op.InBounds ctx.raw}
    {dst : Riscv} {hdst : Riscv.propertiesOf dst = RISCVImmediateProperties} {immVal : Int}
    {resFn : Data.RISCV.Reg → Data.RISCV.Reg}
    {pattern : LocalRewritePattern OpCode}
    {hReturnOps : pattern.ReturnOps}
    {hReturnCtx : pattern.ReturnCtxChanges} {hReturnVIB : pattern.ReturnValuesInBounds}
    {hReturnV : pattern.ReturnValues}
    {newCtx : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {state newState : InterpreterState ctx} {state' : InterpreterState newCtx}
    {xVal : Data.LLVM.Int 64} {srcVal : Data.LLVM.Int 1}
    {ipIn : (InsertPoint.before op).InBounds ctx.raw}
    {ipIn' : (InsertPoint.before op).InBounds newCtx.raw}
    (hpatternOrig : pattern ctx op = some (newCtx, some (newOps, newValues)))
    (hEmit : sltiEmitLocal op lhs dst hdst immVal false ctx
      = some (newCtx, some (newOps, newValues)))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩)
    (hLhsInBounds : lhs.InBounds ctx.raw)
    (hxVal : state.variables.getVar? lhs = some (RuntimeValue.int 64 xVal))
    (_hRes : newState.variables.getVar? (op.getResult 0) = some (RuntimeValue.int 1 srcVal))
    (hMem : state.memory = newState.memory)
    (memoryRefinement : state.memory = state'.memory)
    (hDomCtxLhs : lhs.dominatesIp (InsertPoint.before op) ctx)
    (lhsNotOp : ¬ lhs ∈ op.getResults! ctx.raw)
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) ipIn')
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpatternOrig hReturnVIB hReturnV hReturnCtx)
      (.at (.before op)) (.at (.before op)) ipIn ipIn')
    (hSemR : ∀ (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr)
        (mem : MemoryState),
        Riscv.interpretOp' dst
            (cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk immVal (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (resFn r)], mem, none)))
    (hData : -2048 ≤ immVal → immVal ≤ 2047 → ∀ xt : Data.LLVM.Int 64, xVal ⊒ xt →
        srcVal ⊒ RISCV.Reg.toInt (resFn (LLVM.Int.toReg xt)) 1) :
    ∃ newState', interpretOpList newOps.toList state'
        (by grind [LocalRewritePattern.ReturnOps]) = some (newState', none) ∧
      newState.memory = newState'.memory ∧
      ∃ targetValues, newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
        (#[RuntimeValue.int 1 srcVal] : Array RuntimeValue) ⊒ targetValues := by
  simp only [sltiEmitLocal, Bool.false_eq_true, reduceIte] at hEmit
  simp only [bind, pure] at hEmit
  -- The immediate range guard (bail branch is impossible once we reached `some (...)`).
  split at hEmit
  · simp at hEmit
  rename_i hRange
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hRange
  have hlo : -2048 ≤ immVal := by omega
  have hhi : immVal ≤ 2047 := by omega
  -- Peel the three creations: `castToReg lhs → dst (imm) → castBack`.
  peelCastToRegLocal hEmit ctx₁ castOp hCast hDomCtxLhs hDom₁
  peelOpCreation! hEmit ctx₂ immOp hImm hDom₁ hDom₂
  peelReplaceWithRegLocal hEmit ctx₃ castBackOp hCastBack hDom₂ hDom₃
  cleanupHpattern hEmit
  -- Read the refined value `xt` of `lhs` in the target state `state'`.
  obtain ⟨xt, hOpVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtxLhs hDom₃ lhsNotOp
  -- Structural facts about the three created ops.
  have hCastType : castOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
  have hImmType : immOp.getOpType! ctx₃.raw = .riscv dst := by grind
  have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastOperands : castOp.getOperands! ctx₃.raw = #[lhs] := by grind
  have hImmOperands :
      immOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (immOp.getResult 0)] := by grind
  have hImmProps : immOp.getProperties! ctx₃.raw (.riscv dst)
      = cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk immVal (IntegerType.mk 64)))
      := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hImm (operation := immOp)]
  have isT : Attribute.isType (Attribute.integerType (⟨1⟩ : IntegerType)) := by grind
  have hCBType : ((op.getResult 0).get! ctx₂.raw).type
      = (⟨Attribute.integerType ⟨1⟩, isT⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hImm
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCast
          (value := ValuePtr.opResult (op.getResult 0))]
    have h2 := hResType
    simp only [ValuePtr.getType!_opResult] at h1
    apply Subtype.ext
    rw [h1]; exact h2
  have hCastResTypes : castOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hImm (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hImmResTypes : immOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hImm (operation := immOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := immOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
      = #[⟨Attribute.integerType ⟨1⟩, isT⟩] := by grind
  -- Interpretation tail: `interpretOpList [castOp, immOp, castBackOp]` in `state'`.
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hOpVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := resFn (LLVM.Int.toReg xt))
      (props := cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk immVal (IntegerType.mk 64))))
      (hSemR (LLVM.Int.toReg xt))
      hImmType hImmProps hImmOperands hImmResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₂
  refine ⟨s₃, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt (resFn (LLVM.Int.toReg xt)) 1)], ?_, ?_⟩
    · simp [hRes₃, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using hData hlo hhi xt hxtRef⟩

set_option maxHeartbeats 1600000 in
theorem sltiEmitLocal_wrap_sound {ctx : WfIRContext OpCode} (_ctxDom : ctx.Dom)
    {op : OperationPtr} {lhs : ValuePtr} {opInBounds : op.InBounds ctx.raw}
    {dst : Riscv} {hdst : Riscv.propertiesOf dst = RISCVImmediateProperties} {immVal : Int}
    {resCmp : Data.RISCV.Reg → Data.RISCV.Reg}
    {pattern : LocalRewritePattern OpCode}
    {hReturnOps : pattern.ReturnOps}
    {hReturnCtx : pattern.ReturnCtxChanges} {hReturnVIB : pattern.ReturnValuesInBounds}
    {hReturnV : pattern.ReturnValues}
    {newCtx : WfIRContext OpCode} {newOps : Array OperationPtr} {newValues : Array ValuePtr}
    {state newState : InterpreterState ctx} {state' : InterpreterState newCtx}
    {xVal : Data.LLVM.Int 64} {srcVal : Data.LLVM.Int 1}
    {ipIn : (InsertPoint.before op).InBounds ctx.raw}
    {ipIn' : (InsertPoint.before op).InBounds newCtx.raw}
    (hpatternOrig : pattern ctx op = some (newCtx, some (newOps, newValues)))
    (hEmit : sltiEmitLocal op lhs dst hdst immVal true ctx
      = some (newCtx, some (newOps, newValues)))
    (hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩)
    (hLhsInBounds : lhs.InBounds ctx.raw)
    (hxVal : state.variables.getVar? lhs = some (RuntimeValue.int 64 xVal))
    (hMem : state.memory = newState.memory)
    (memoryRefinement : state.memory = state'.memory)
    (hDomCtxLhs : lhs.dominatesIp (InsertPoint.before op) ctx)
    (lhsNotOp : ¬ lhs ∈ op.getResults! ctx.raw)
    (state'Dom : state'.DefinesDominating (InsertPoint.before op) ipIn')
    (valueRefinement : state.variables.isRefinedByAt state'.variables
      (LocalRewritePattern.mapping hpatternOrig hReturnVIB hReturnV hReturnCtx)
      (.at (.before op)) (.at (.before op)) ipIn ipIn')
    (hSemR : ∀ (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr) (blockOperands : Array BlockPtr)
        (mem : MemoryState),
        Riscv.interpretOp' dst
            (cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk immVal (IntegerType.mk 64))))
            resultTypes #[.reg r] blockOperands mem
          = some (.ok (#[.reg (resCmp r)], mem, none)))
    (hData : -2048 ≤ immVal → immVal ≤ 2047 → ∀ xt : Data.LLVM.Int 64, xVal ⊒ xt →
        srcVal ⊒ RISCV.Reg.toInt
          (Data.RISCV.xori (BitVec.ofInt 12 1) (resCmp (LLVM.Int.toReg xt))) 1) :
    ∃ newState', interpretOpList newOps.toList state'
        (by grind [LocalRewritePattern.ReturnOps]) = some (newState', none) ∧
      newState.memory = newState'.memory ∧
      ∃ targetValues, newValues.mapM (newState'.variables.getVar? ·) = some targetValues ∧
        (#[RuntimeValue.int 1 srcVal] : Array RuntimeValue) ⊒ targetValues := by
  simp only [sltiEmitLocal, reduceIte] at hEmit
  simp only [bind, pure] at hEmit
  split at hEmit
  · simp at hEmit
  rename_i hRange
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hRange
  have hlo : -2048 ≤ immVal := by omega
  have hhi : immVal ≤ 2047 := by omega
  -- Peel the four creations: `castToReg lhs → dst (imm) → xori _ 1 → castBack`.
  peelCastToRegLocal hEmit ctx₁ castOp hCast hDomCtxLhs hDom₁
  peelOpCreation! hEmit ctx₂ immOp hImm hDom₁ hDom₂
  peelOpCreation! hEmit ctx₃ xorOp hXor hDom₂ hDom₃
  peelReplaceWithRegLocal hEmit ctx₄ castBackOp hCastBack hDom₃ hDom₄
  cleanupHpattern hEmit
  obtain ⟨xt, hOpVal', hxtRef⟩ :=
    LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hxVal
      hDomCtxLhs hDom₄ lhsNotOp
  have hCastType : castOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by grind
  have hImmType : immOp.getOpType! ctx₄.raw = .riscv dst := by grind
  have hXorType : xorOp.getOpType! ctx₄.raw = .riscv .xori := by grind
  have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
    grind
  have hCastOperands : castOp.getOperands! ctx₄.raw = #[lhs] := by grind
  have hImmOperands :
      immOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (castOp.getResult 0)] := by grind
  have hXorOperands :
      xorOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (immOp.getResult 0)] := by grind
  have hCastBackOperands :
      castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (xorOp.getResult 0)] := by grind
  have hImmProps : immOp.getProperties! ctx₄.raw (.riscv dst)
      = cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk immVal (IntegerType.mk 64)))
      := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
      OperationPtr.getProperties!_WfRewriter_createOp_ne hXor (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hImm (operation := immOp)]
  have hXorProps : xorOp.getProperties! ctx₄.raw (.riscv .xori)
      = RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)) := by
    rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
    grind [OperationPtr.getProperties!_WfRewriter_createOp hXor (operation := xorOp)]
  have isT : Attribute.isType (Attribute.integerType (⟨1⟩ : IntegerType)) := by grind
  have hCBType : ((op.getResult 0).get! ctx₃.raw).type
      = (⟨Attribute.integerType ⟨1⟩, isT⟩ : TypeAttr) := by
    have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
        = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
      grind [ValuePtr.getType!_WfRewriter_createOp hImm
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hXor
          (value := ValuePtr.opResult (op.getResult 0)),
        ValuePtr.getType!_WfRewriter_createOp hCast
          (value := ValuePtr.opResult (op.getResult 0))]
    simp only [ValuePtr.getType!_opResult] at h1
    apply Subtype.ext
    rw [h1]; exact hResType
  have hCastResTypes : castOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCast (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hImm (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := castOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := castOp)]
  have hImmResTypes : immOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hImm (operation := immOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := immOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := immOp)]
  have hXorResTypes : xorOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
    grind [OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := xorOp),
      OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xorOp)]
  have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
      = #[⟨Attribute.integerType ⟨1⟩, isT⟩] := by grind
  have hSemXori : ∀ (r : Data.RISCV.Reg) (resultTypes : Array TypeAttr)
      (blockOperands : Array BlockPtr) (mem : MemoryState),
      Riscv.interpretOp' .xori (RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)))
          resultTypes #[.reg r] blockOperands mem
        = some (.ok (#[.reg (Data.RISCV.xori (BitVec.ofInt 12 1) r)], mem, none)) := by
    intro r rt bo mem; simp [Riscv.interpretOp', pure, Interp]
  obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
    interpretOp_castToReg_forward (state := state') (inBounds := by grind)
      hCastType hCastOperands hCastResTypes hOpVal'
  obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
      (res := resCmp (LLVM.Int.toReg xt))
      (props := cast hdst.symm (RISCVImmediateProperties.mk (IntegerAttr.mk immVal (IntegerType.mk 64))))
      (hSemR (LLVM.Int.toReg xt))
      hImmType hImmProps hImmOperands hImmResTypes hRes₁
  obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
    interpretOp_riscv_unaryReg_imm_forward (state := s₂) (inBounds := by grind) (rop := Riscv.xori)
      (res := Data.RISCV.xori (BitVec.ofInt 12 1) (resCmp (LLVM.Int.toReg xt)))
      (props := RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)))
      (hSemXori (resCmp (LLVM.Int.toReg xt)))
      hXorType hXorProps hXorOperands hXorResTypes hRes₂
  obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
    interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
      hCastBackType hCastBackOperands hCastBackResTypes hRes₃
  refine ⟨s₄, ?_, by grind, ?_⟩
  · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
  · refine ⟨#[RuntimeValue.int 1
        (RISCV.Reg.toInt (Data.RISCV.xori (BitVec.ofInt 12 1) (resCmp (LLVM.Int.toReg xt))) 1)],
        ?_, ?_⟩
    · simp [hRes₄, Option.bind, Option.map]
    · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using hData hlo hhi xt hxtRef⟩

/-! ### Correctness of `slti_local` -/

set_option maxHeartbeats 1600000 in
theorem slti_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps slti_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges slti_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds slti_local}
    {h₄ : LocalRewritePattern.ReturnValues slti_local} :
    LocalRewritePattern.PreservesSemantics slti_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  -- Work on a copy `hEmitPat` of the pattern, unfolded so the matcher and guards can be peeled;
  -- `hpattern` itself stays in `slti_local ctx op = …` form for the `mapping` in `valueRefinement`.
  have hEmitPat := hpattern
  simp only [slti_local] at hEmitPat
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
  have ⟨hNRes, hNOper, hNSucc, hNReg, ⟨i1ty, hResType, hResBw⟩, hOpEqType⟩ :=
    OperationPtr.Verified.llvm_icmp opVerif hOpType
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  -- The lhs-type guard: `lhs.getType!.val = integerType lt`.
  rw [hOperand0, hOperand1] at hOpEqType
  -- Peel the `.integerType lt` match on `lhs`'s type.
  have hLhsTySome : ∃ lt, (lhs.getType! ctx.raw).val = Attribute.integerType lt := by
    cases hlt : (lhs.getType! ctx.raw).val with
    | integerType lt => exact ⟨lt, rfl⟩
    | _ => rw [hlt] at hEmitPat; simp at hEmitPat
  obtain ⟨lt, hLhsType⟩ := hLhsTySome
  simp only [hLhsType] at hEmitPat
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType lt := by
    rw [← hOpEqType, hLhsType]
  -- The bitwidth guard: `lt.bitwidth = 64`.
  peelSplittableCondition' [hBw] hEmitPat
  -- Peel the constant match on the rhs.
  have hCVSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hCV : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hCV] at hEmitPat; simp at hEmitPat
  obtain ⟨cst, hCV⟩ := Option.isSome_iff_exists.mp hCVSome
  rw [hCV] at hEmitPat
  simp only [] at hEmitPat
  -- Unfold the interpretation of the source `icmp`: exposes both operand values.
  obtain ⟨xVal, yVal, hxVal, hyVal, hMem, hRes, hCf⟩ :=
    matchIcmp_interpretOp_unfold opInBounds hOpType hNumResults hOperands hProps hinterp
      hLhsType hRhsType
  subst hCf
  -- Pin the rhs's runtime value to the matched constant via `EquationLemmaAt`.
  have hyConst := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds stateWf
    hCV (by rw [hOperands]; simp) hRhsType
  obtain rfl : yVal = Data.LLVM.Int.constant lt.bitwidth cst.value := by
    have h := hyVal.symm.trans hyConst; simpa using h
  -- The value operand `lhs` dominates the rewrite point in the source context.
  have hDomCtxLhs : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  -- Source value: `op`'s single result is `icmp x (const c) pred`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by grind]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  have lhsNotOp : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  obtain ⟨bw⟩ := lt; simp only at hBw; subst hBw
  have hResType1 : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := i1ty; simp only at hResBw; subst hResBw; exact hResType
  have hLhsInBounds : lhs.InBounds ctx.raw := by rw [← hOperand0]; grind
  -- Dispatch on the comparison predicate; each arm delegates to the shared emit lemmas.
  split at hEmitPat
  · rw [show prop.predicate = Data.LLVM.IntPred.slt from by assumption] at hRes ⊢
    exact sltiEmitLocal_noWrap_sound ctxDom hpattern hEmitPat hResType1 hLhsInBounds hxVal hRes hMem
      memoryRefinement hDomCtxLhs lhsNotOp state'Dom valueRefinement (fun _ _ _ _ => rfl)
      (fun hlo hhi xt hxt => icmp_slt_isRefinedBy_toInt_slti cst.value hlo hhi hxt)
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄) (opInBounds := opInBounds)
  · rw [show prop.predicate = Data.LLVM.IntPred.ult from by assumption] at hRes ⊢
    exact sltiEmitLocal_noWrap_sound ctxDom hpattern hEmitPat hResType1 hLhsInBounds hxVal hRes hMem
      memoryRefinement hDomCtxLhs lhsNotOp state'Dom valueRefinement (fun _ _ _ _ => rfl)
      (fun hlo hhi xt hxt => icmp_ult_isRefinedBy_toInt_sltiu cst.value hlo hhi hxt)
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄) (opInBounds := opInBounds)
  · rw [show prop.predicate = Data.LLVM.IntPred.sge from by assumption] at hRes ⊢
    exact sltiEmitLocal_wrap_sound ctxDom hpattern hEmitPat hResType1 hLhsInBounds hxVal hMem
      memoryRefinement hDomCtxLhs lhsNotOp state'Dom valueRefinement (fun _ _ _ _ => rfl)
      (fun hlo hhi xt hxt => icmp_sge_isRefinedBy_toInt_slti cst.value hlo hhi hxt)
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄) (opInBounds := opInBounds)
  · rw [show prop.predicate = Data.LLVM.IntPred.uge from by assumption] at hRes ⊢
    exact sltiEmitLocal_wrap_sound ctxDom hpattern hEmitPat hResType1 hLhsInBounds hxVal hMem
      memoryRefinement hDomCtxLhs lhsNotOp state'Dom valueRefinement (fun _ _ _ _ => rfl)
      (fun hlo hhi xt hxt => icmp_uge_isRefinedBy_toInt_sltiu cst.value hlo hhi hxt)
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄) (opInBounds := opInBounds)
  · rw [show prop.predicate = Data.LLVM.IntPred.sle from by assumption] at hRes ⊢
    exact sltiEmitLocal_noWrap_sound ctxDom hpattern hEmitPat hResType1 hLhsInBounds hxVal hRes hMem
      memoryRefinement hDomCtxLhs lhsNotOp state'Dom valueRefinement (fun _ _ _ _ => rfl)
      (fun hlo hhi xt hxt => icmp_sle_isRefinedBy_toInt_slti cst.value hlo hhi hxt)
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄) (opInBounds := opInBounds)
  · rw [show prop.predicate = Data.LLVM.IntPred.ule from by assumption] at hRes ⊢
    split at hEmitPat
    · simp at hEmitPat
    rename_i hNeg
    exact sltiEmitLocal_noWrap_sound ctxDom hpattern hEmitPat hResType1 hLhsInBounds hxVal hRes hMem
      memoryRefinement hDomCtxLhs lhsNotOp state'Dom valueRefinement (fun _ _ _ _ => rfl)
      (fun hlo hhi xt hxt => icmp_ule_isRefinedBy_toInt_sltiu cst.value hlo hhi hNeg hxt)
      (hReturnOps := h) (hReturnCtx := h₂) (hReturnVIB := h₃) (hReturnV := h₄) (opInBounds := opInBounds)
  · simp at hEmitPat

end Veir
