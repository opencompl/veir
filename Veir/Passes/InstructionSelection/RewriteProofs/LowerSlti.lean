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

namespace Veir

theorem signExtend_ofInt_12_64s (c : Int) (hlo : -2048 ≤ c) (hhi : c ≤ 2047) :
    BitVec.signExtend 64 (BitVec.ofInt 12 c) = BitVec.ofInt 64 c := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_ofInt, BitVec.toInt_ofInt,
    show (2 ^ 12 : Nat) = 4096 from rfl, show (2 ^ 64 : Nat) = 18446744073709551616 from rfl]
  simp only [Int.bmod]; omega

/-- `icmp`-specialised interpretation unfold. Like `matchShiftOp_interpretOp_unfold`, the interpreter
    permits the two operands to have different integer widths (`intType`/`intType2`) and a successful
    interpretation forces them equal (`h'`); unlike it, the result has fixed type `i1` and value
    `LLVM.Int.icmp x y props.predicate`. -/
theorem matchIcmp_interpretOp_unfold {ctx : WfIRContext OpCode}
    {op : OperationPtr} {lhs rhs : ValuePtr} {props : propertiesOf (.llvm .icmp)} {intType intType2}
    {state newState : InterpreterState ctx} {cf} (opInBounds : op.InBounds ctx.raw)
    (hOpType : op.getOpType! ctx.raw = .llvm .icmp)
    (hNumResults : op.getNumResults! ctx.raw = 1)
    (hOperands : op.getOperands! ctx.raw = #[lhs, rhs])
    (hProps : props = op.getProperties! ctx.raw (.llvm .icmp))
    (hinterp : interpretOp op state opInBounds = some (.ok (newState, cf)))
    (hLhsType : (lhs.getType! ctx.raw).val = Attribute.integerType intType)
    (hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType intType2) :
    ∃ (x : Data.LLVM.Int intType.bitwidth) (y : Data.LLVM.Int intType2.bitwidth)
      (h' : intType2.bitwidth = intType.bitwidth),
      state.variables.getVar? lhs = some (RuntimeValue.int intType.bitwidth x) ∧
      state.variables.getVar? rhs = some (RuntimeValue.int intType2.bitwidth y) ∧
      state.memory = newState.memory ∧
      newState.variables.getVar? (op.getResult 0) =
        some (RuntimeValue.int 1 (Data.LLVM.Int.icmp x (Data.LLVM.Int.cast y h') props.predicate)) ∧
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
  rw [show rhs.getType! ctx.raw = ⟨.integerType intType2, hRhsType ▸ (rhs.getType! ctx.raw).2⟩
        from Subtype.ext hRhsType] at hrconf
  obtain ⟨y, rfl⟩ := RuntimeValue.Conforms.integerType hrconf
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]
    grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOpVals : state.variables.getOperandValues op
      = some #[RuntimeValue.int intType.bitwidth x, RuntimeValue.int intType2.bitwidth y] := by
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
  simp only [← hProps, interpretOp', Llvm.interpretOp'] at hInterp'
  split at hInterp'
  · simp at hInterp'
  rename_i hbw
  have h' : intType2.bitwidth = intType.bitwidth := by simpa using hbw
  obtain ⟨rfl, rfl, rfl⟩ :
      resValues = #[RuntimeValue.int 1 (Data.LLVM.Int.icmp x (Data.LLVM.Int.cast y h') props.predicate)] ∧
      mem' = state.memory ∧ cf = none := by
    simp only [pure, Interp] at hInterp'; grind
  subst hNew
  refine ⟨x, y, h', hlGetVar, hrGetVar, rfl, ?_, rfl⟩
  rw [VariableState.getVar?_getResult_of_setResultValues? (by rw [hNumResults]; omega) hSet]
  simp

theorem slti_slt {x xt : Data.LLVM.Int 64} (c : Int) (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) .slt
      ⊒ RISCV.Reg.toInt (Data.RISCV.slti (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 1 := by
  rw [Data.RISCV.slti, signExtend_ofInt_12_64s c hlo hhi]
  simp only [Data.LLVM.Int.constant]; generalize BitVec.ofInt 64 c = v; revert h; veir_bv_decide

theorem sltiu_ult {x xt : Data.LLVM.Int 64} (c : Int) (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) .ult
      ⊒ RISCV.Reg.toInt (Data.RISCV.sltiu (BitVec.ofInt 12 c) (LLVM.Int.toReg xt)) 1 := by
  rw [Data.RISCV.sltiu, signExtend_ofInt_12_64s c hlo hhi]
  simp only [Data.LLVM.Int.constant]; generalize BitVec.ofInt 64 c = v; revert h; veir_bv_decide

theorem slti_sge {x xt : Data.LLVM.Int 64} (c : Int) (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) .sge
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.xori (BitVec.ofInt 12 1) (Data.RISCV.slti (BitVec.ofInt 12 c) (LLVM.Int.toReg xt))) 1 := by
  rw [Data.RISCV.xori, Data.RISCV.slti, signExtend_ofInt_12_64s c hlo hhi]
  simp only [Data.LLVM.Int.constant]; generalize BitVec.ofInt 64 c = v; revert h; veir_bv_decide

theorem sltiu_uge {x xt : Data.LLVM.Int 64} (c : Int) (hlo : -2048 ≤ c) (hhi : c ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) .uge
      ⊒ RISCV.Reg.toInt
          (Data.RISCV.xori (BitVec.ofInt 12 1) (Data.RISCV.sltiu (BitVec.ofInt 12 c) (LLVM.Int.toReg xt))) 1 := by
  rw [Data.RISCV.xori, Data.RISCV.sltiu, signExtend_ofInt_12_64s c hlo hhi]
  simp only [Data.LLVM.Int.constant]; generalize BitVec.ofInt 64 c = v; revert h; veir_bv_decide

/-- `ofInt (c+1) = ofInt c + 1` — a ring identity, used to relate `x ≤ c` to `x < c+1`. -/
theorem ofInt_succ_bridge (c : Int) :
    BitVec.ofInt 64 (c + 1) = BitVec.ofInt 64 c + 1 := by
  simp [BitVec.ofInt_add]

theorem slti_sle {x xt : Data.LLVM.Int 64} (c : Int) (hlo : -2048 ≤ c + 1) (hhi : c + 1 ≤ 2047) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) .sle
      ⊒ RISCV.Reg.toInt (Data.RISCV.slti (BitVec.ofInt 12 (c + 1)) (LLVM.Int.toReg xt)) 1 := by
  -- `x ≤s c ↔ x <s c+1` needs `c ≠ maxInt`; since `c ≤ 2046` its bit-pattern is not `0x7FFF…F`.
  have hb : (BitVec.ofInt 64 c) ≠ BitVec.ofInt 64 9223372036854775807 := by
    intro heq
    have hh : (BitVec.ofInt 64 c).toInt = (BitVec.ofInt 64 9223372036854775807).toInt := by rw [heq]
    rw [BitVec.toInt_ofInt, BitVec.toInt_ofInt,
      show (2 ^ 64 : Nat) = 18446744073709551616 from rfl] at hh
    simp only [Int.bmod] at hh; omega
  rw [Data.RISCV.slti, signExtend_ofInt_12_64s (c + 1) hlo hhi, ofInt_succ_bridge]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v at hb ⊢
  revert h hb; veir_bv_decide

theorem sltiu_ule {x xt : Data.LLVM.Int 64} (c : Int)
    (hlo : -2048 ≤ c + 1) (hhi : c + 1 ≤ 2047) (hc : c ≠ -1) (h : x ⊒ xt) :
    Data.LLVM.Int.icmp x (Data.LLVM.Int.constant 64 c) .ule
      ⊒ RISCV.Reg.toInt (Data.RISCV.sltiu (BitVec.ofInt 12 (c + 1)) (LLVM.Int.toReg xt)) 1 := by
  have hcu : (BitVec.ofInt 64 c) ≠ BitVec.ofInt 64 (-1) := by
    intro heq; apply hc
    have hh : (BitVec.ofInt 64 c).toInt = (BitVec.ofInt 64 (-1)).toInt := by rw [heq]
    rw [BitVec.toInt_ofInt, BitVec.toInt_ofInt,
      show (2 ^ 64 : Nat) = 18446744073709551616 from rfl] at hh
    simp only [Int.bmod] at hh; omega
  rw [Data.RISCV.sltiu, signExtend_ofInt_12_64s (c + 1) hlo hhi, ofInt_succ_bridge]
  simp only [Data.LLVM.Int.constant]
  generalize BitVec.ofInt 64 c = v at hcu ⊢
  revert h hcu; veir_bv_decide

set_option hygiene false in
/-- Shared non-wrap `slti`-family arm (`slt`/`ult`/`sle`/`ule`): after the predicate `split` and the
    immediate-range guard, peel the 3-op `castToReg → dst(imm) → castBack` chain (via `rw`-based bind
    extraction, which composes with the predicate-dispatch `split` where `simp only [bind_eq_some_iff]`
    does not) and discharge the refinement. `rop`/`sfn` are the RISC-V opcode and its semantic
    function, `imm` the emitted immediate, `lem` the data-refinement term. -/
local macro "sltiNonWrapArm" rop:term ", " sfn:term ", " imm:term ", " lem:term : tactic =>
  `(tactic| (
    split at hpattern
    case isTrue h => simp at hpattern
    rename_i hRange
    obtain ⟨hLo, hHi⟩ : -2048 ≤ $imm ∧ $imm ≤ 2047 := by
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hRange
      omega
    rw [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₁, xCastOp⟩, hCastX, hpattern⟩ := hpattern
    simp only [] at hpattern
    rw [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₂, cmpOp⟩, hCmp, hpattern⟩ := hpattern
    simp only [] at hpattern
    rw [if_neg (by decide)] at hpattern
    rw [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₃, castBackOp⟩, hCastBack, hpattern⟩ := hpattern
    simp only [castToRegLocal] at hCastX
    rw [WfRewriter.createOp!_none_eq (by grind) (by simp) (by simp)] at hCastX
    have hDomLhs₁ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastX
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomLhs
    rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
      (by clear hpattern; simp)] at hCmp
    have hDomLhs₂ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCmp
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomLhs₁
    simp only [replaceWithRegLocal] at hCastBack
    rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
      (by clear hpattern; simp)] at hCastBack
    have hDomLhs₃ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomLhs₂
    cleanupHpattern hpattern
    rw [hpred]
    obtain ⟨xt, hXVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
        hDomLhs hDomLhs₃ vNotOpLhs
    have hCastXType : xCastOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hCmpType : cmpOp.getOpType! ctx₃.raw = .riscv $rop := by grind
    have hCastBackType : castBackOp.getOpType! ctx₃.raw = .builtin .unrealized_conversion_cast := by grind
    have hCastXOperands : xCastOp.getOperands! ctx₃.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hCastX (operation := xCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCmp (operation := xCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
    have hCmpOperands : cmpOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hCmp (operation := cmpOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := cmpOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₃.raw = #[ValuePtr.opResult (cmpOp.getResult 0)] := by grind
    have hCmpProps : cmpOp.getProperties! ctx₃.raw (.riscv $rop)
        = RISCVImmediateProperties.mk (IntegerAttr.mk $imm (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hCmp (operation := cmpOp)]
    have hCBType : ((op.getResult 0).get! ctx₂.raw).type
        = (⟨Attribute.integerType ⟨1⟩, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₂.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hCmp (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCastX (value := ValuePtr.opResult (op.getResult 0))]
      rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
      rw [h1]; exact Subtype.ext hResType
    have hCastXResTypes : xCastOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastX (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCmp (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
    have hCmpResTypes : cmpOp.getResultTypes! ctx₃.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCmp (operation := cmpOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := cmpOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₃.raw
        = #[⟨Attribute.integerType ⟨1⟩, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastXType hCastXOperands hCastXResTypes hXVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := $sfn (BitVec.ofInt 12 $imm) (LLVM.Int.toReg xt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hCmpType hCmpProps hCmpOperands hCmpResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_castBack_forward (state := s₂) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₂
    refine ⟨s₃, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt ($sfn (BitVec.ofInt 12 $imm) (LLVM.Int.toReg xt)) 1)],
        ?_, ?_⟩
      · simp [hRes₃, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using $lem⟩
  ))

set_option hygiene false in
/-- Shared wrap `slti`-family arm (`sge`/`uge`): like `sltiNonWrapArm` but the emit inverts the sense
    with a trailing `xori _ 1`, giving a 4-op `castToReg → dst(imm) → xori 1 → castBack` chain. -/
local macro "sltiWrapArm" rop:term ", " sfn:term ", " imm:term ", " lem:term : tactic =>
  `(tactic| (
    split at hpattern
    case isTrue h => simp at hpattern
    rename_i hRange
    obtain ⟨hLo, hHi⟩ : -2048 ≤ $imm ∧ $imm ≤ 2047 := by
      simp only [Bool.not_eq_true, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hRange
      omega
    rw [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₁, xCastOp⟩, hCastX, hpattern⟩ := hpattern
    simp only [] at hpattern
    rw [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₂, cmpOp⟩, hCmp, hpattern⟩ := hpattern
    simp only [] at hpattern
    rw [if_pos (by decide)] at hpattern
    rw [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₃, xorOp⟩, hXor, hpattern⟩ := hpattern
    simp only [] at hpattern
    rw [Option.bind_eq_some_iff] at hpattern
    obtain ⟨⟨ctx₄, castBackOp⟩, hCastBack, hpattern⟩ := hpattern
    simp only [castToRegLocal] at hCastX
    rw [WfRewriter.createOp!_none_eq (by grind) (by simp) (by simp)] at hCastX
    have hDomLhs₁ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastX
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomLhs
    rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
      (by clear hpattern; simp)] at hCmp
    have hDomLhs₂ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCmp
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomLhs₁
    rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
      (by clear hpattern; simp)] at hXor
    have hDomLhs₃ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hXor
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomLhs₂
    simp only [replaceWithRegLocal] at hCastBack
    rw [WfRewriter.createOp!_none_eq (by clear hpattern; grind) (by clear hpattern; simp)
      (by clear hpattern; simp)] at hCastBack
    have hDomLhs₄ := (ValuePtr.dominatesIp_before_WfRewriter_createOp hCastBack
      (by clear hpattern; grind) (by clear hpattern; grind)).mpr hDomLhs₃
    cleanupHpattern hpattern
    rw [hpred]
    obtain ⟨xt, hXVal', hxtRef⟩ :=
      LocalRewritePattern.exists_refined_int_getVar? valueRefinement state'Dom (by grind) hlVal
        hDomLhs hDomLhs₄ vNotOpLhs
    have hCastXType : xCastOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hCastX (operation := xCastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCmp (operation := xCastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := xCastOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := xCastOp)]
    have hCmpType : cmpOp.getOpType! ctx₄.raw = .riscv $rop := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hCmp (operation := cmpOp),
        OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := cmpOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := cmpOp)]
    have hXorType : xorOp.getOpType! ctx₄.raw = .riscv .xori := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hXor (operation := xorOp),
        OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := xorOp)]
    have hCastBackType : castBackOp.getOpType! ctx₄.raw = .builtin .unrealized_conversion_cast := by
      grind [OperationPtr.getOpType!_WfRewriter_createOp hCastBack (operation := castBackOp)]
    have hCastXOperands : xCastOp.getOperands! ctx₄.raw = #[lhs] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hCastX (operation := xCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCmp (operation := xCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := xCastOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xCastOp)]
    have hCmpOperands : cmpOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (xCastOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hCmp (operation := cmpOp),
        OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := cmpOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := cmpOp)]
    have hXorOperands : xorOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (cmpOp.getResult 0)] := by
      grind [OperationPtr.getOperands!_WfRewriter_createOp hXor (operation := xorOp),
        OperationPtr.getOperands!_WfRewriter_createOp hCastBack (operation := xorOp)]
    have hCastBackOperands :
        castBackOp.getOperands! ctx₄.raw = #[ValuePtr.opResult (xorOp.getResult 0)] := by grind
    have hCmpProps : cmpOp.getProperties! ctx₄.raw (.riscv $rop)
        = RISCVImmediateProperties.mk (IntegerAttr.mk $imm (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind),
        OperationPtr.getProperties!_WfRewriter_createOp_ne hXor (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hCmp (operation := cmpOp)]
    have hXorProps : xorOp.getProperties! ctx₄.raw (.riscv .xori)
        = RISCVImmediateProperties.mk (IntegerAttr.mk 1 (IntegerType.mk 64)) := by
      rw [OperationPtr.getProperties!_WfRewriter_createOp_ne hCastBack (by grind)]
      grind [OperationPtr.getProperties!_WfRewriter_createOp hXor (operation := xorOp)]
    have hCBType : ((op.getResult 0).get! ctx₃.raw).type
        = (⟨Attribute.integerType ⟨1⟩, by grind⟩ : TypeAttr) := by
      have h1 : (ValuePtr.opResult (op.getResult 0)).getType! ctx₃.raw
          = (ValuePtr.opResult (op.getResult 0)).getType! ctx.raw := by
        grind [ValuePtr.getType!_WfRewriter_createOp hXor (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCmp (value := ValuePtr.opResult (op.getResult 0)),
          ValuePtr.getType!_WfRewriter_createOp hCastX (value := ValuePtr.opResult (op.getResult 0))]
      rw [ValuePtr.getType!_opResult, ValuePtr.getType!_opResult] at h1
      rw [h1]; exact Subtype.ext hResType
    have hCastXResTypes : xCastOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCastX (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCmp (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := xCastOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xCastOp)]
    have hCmpResTypes : cmpOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hCmp (operation := cmpOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := cmpOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := cmpOp)]
    have hXorResTypes : xorOp.getResultTypes! ctx₄.raw = #[⟨Attribute.registerType ⟨none⟩, rfl⟩] := by
      grind [OperationPtr.getResultTypes!_WfRewriter_createOp hXor (operation := xorOp),
        OperationPtr.getResultTypes!_WfRewriter_createOp hCastBack (operation := xorOp)]
    have hCastBackResTypes : castBackOp.getResultTypes! ctx₄.raw
        = #[⟨Attribute.integerType ⟨1⟩, by grind⟩] := by grind
    obtain ⟨s₁, hI₁, hMem₁, hRes₁, -⟩ :=
      interpretOp_castToReg_forward (state := state') (inBounds := by grind)
        hCastXType hCastXOperands hCastXResTypes hXVal'
    obtain ⟨s₂, hI₂, hMem₂, hRes₂, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₁) (inBounds := by grind)
        (res := $sfn (BitVec.ofInt 12 $imm) (LLVM.Int.toReg xt))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hCmpType hCmpProps hCmpOperands hCmpResTypes hRes₁
    obtain ⟨s₃, hI₃, hMem₃, hRes₃, -⟩ :=
      interpretOp_riscv_unaryReg_imm_forward (state := s₂) (inBounds := by grind)
        (res := Data.RISCV.xori (BitVec.ofInt 12 1) ($sfn (BitVec.ofInt 12 $imm) (LLVM.Int.toReg xt)))
        (fun _ _ _ => by simp [Riscv.interpretOp', Interp, pure])
        hXorType hXorProps hXorOperands hXorResTypes hRes₂
    obtain ⟨s₄, hI₄, hMem₄, hRes₄, -⟩ :=
      interpretOp_castBack_forward (state := s₃) (inBounds := by grind)
        hCastBackType hCastBackOperands hCastBackResTypes hRes₃
    refine ⟨s₄, ?_, by grind, ?_⟩
    · simp [interpretOpList_cons, hI₁, hI₂, hI₃, hI₄, liftM, monadLift, MonadLift.monadLift, Interp]
    · refine ⟨#[RuntimeValue.int 1 (RISCV.Reg.toInt
        (Data.RISCV.xori (BitVec.ofInt 12 1) ($sfn (BitVec.ofInt 12 $imm) (LLVM.Int.toReg xt))) 1)],
        ?_, ?_⟩
      · simp [hRes₄, Option.bind, Option.map]
      · exact RuntimeValue.arrayIsRefinedBy_singleton.mpr ⟨rfl, by simpa using $lem⟩
  ))

set_option maxHeartbeats 2000000 in
theorem slti_local_preservesSemantics
    {h : LocalRewritePattern.ReturnOps slti_local}
    {h₂ : LocalRewritePattern.ReturnCtxChanges slti_local}
    {h₃ : LocalRewritePattern.ReturnValuesInBounds slti_local}
    {h₄ : LocalRewritePattern.ReturnValues slti_local} :
    LocalRewritePattern.PreservesSemantics slti_local h h₂ h₃ h₄ := by
  simp only [LocalRewritePattern.PreservesSemantics, slti_local]
  intro ctx ctxDom ctxVerif op opInBounds newCtx newOps newValues hpattern state stateWf
    newState cf hinterp
  rintro sourceValues hsourceValues state' state'Wf state'Dom ⟨memoryRefinement, valueRefinement⟩
  simp [liftM, monadLift, MonadLift.monadLift] at hinterp
  simp only [Option.bind_eq_bind, pure] at hpattern
  -- Peel the `matchIcmp`.
  have hMatchSome : (matchIcmp op ctx.raw).isSome := by
    cases hM : matchIcmp op ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨⟨lhs, rhs, prop⟩, hMatch⟩ := Option.isSome_iff_exists.mp hMatchSome
  rw [hMatch] at hpattern
  simp only [] at hpattern
  have ⟨hOpType, hNumResults, hOperands, hPropEq⟩ := matchIcmp_implies hMatch
  have hLhsEq : lhs = (op.getOperands! ctx.raw)[0]! := by rw [hOperands]; rfl
  have hRhsEq : rhs = (op.getOperands! ctx.raw)[1]! := by rw [hOperands]; rfl
  have hOperand0 : op.getOperand! ctx.raw 0 = lhs := by
    rw [hLhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have hOperand1 : op.getOperand! ctx.raw 1 = rhs := by
    rw [hRhsEq]; grind [OperationPtr.getOperand!, OperationPtr.getOperands!]
  have opVerif : op.Verified ctx opInBounds := by grind
  have ⟨hNRes, hNOper, hOpMatch, it, hResIt, hResBw⟩ :=
    OperationPtr.Verified.llvm_icmp opVerif hOpType
  -- `lhs` must have integer type for the pattern to fire.
  obtain ⟨lt, hLhsType⟩ :
      ∃ lt, (lhs.getType! ctx.raw).val = Attribute.integerType lt := by
    cases hr : (lhs.getType! ctx.raw).val with
    | integerType t => exact ⟨t, rfl⟩
    | _ => rw [hr] at hpattern; simp at hpattern
  rw [hLhsType] at hpattern
  simp only [] at hpattern
  -- The width guard fixes `lt.bitwidth = 64`.
  split at hpattern
  case isTrue hne => simp at hpattern
  rename_i hWidth64
  -- Operand types match (verifier): `rhs` also has type `lt`.
  have hRhsType : (rhs.getType! ctx.raw).val = Attribute.integerType lt := by
    rw [← hOperand1, ← hOpMatch, hOperand0, hLhsType]
  -- Pin the matched constant.
  have hCstSome : (matchConstantIntVal rhs ctx.raw).isSome := by
    cases hM : matchConstantIntVal rhs ctx.raw with
    | some y => rfl
    | none => rw [hM] at hpattern; simp at hpattern
  obtain ⟨cst, hCstMatch⟩ := Option.isSome_iff_exists.mp hCstSome
  rw [hCstMatch] at hpattern
  simp only [] at hpattern
  -- Unfold the icmp interpretation.
  obtain ⟨xlv, xrv, h', hlVal, hrVal, hMem, hRes, hCf⟩ :=
    matchIcmp_interpretOp_unfold (props := prop)
      opInBounds hOpType hNumResults hOperands hPropEq hinterp hLhsType hRhsType
  subst hCf
  rw [Data.LLVM.Int.cast_self] at hRes
  -- Pin `rhs`'s runtime value to `constant cst.value`.
  have hrhsVal := matchConstantIntVal_getVar?_of_EquationLemmaAt ctxDom ctxVerif opInBounds
    stateWf hCstMatch (by rw [hOperands]; simp) hRhsType
  obtain rfl : xrv = Data.LLVM.Int.constant lt.bitwidth cst.value := by
    have := hrVal.symm.trans hrhsVal; simpa using this
  -- `lhs` dominates and is not among `op`'s results.
  have hDomLhs : lhs.dominatesIp (InsertPoint.before op) ctx := by
    grind [WfIRContext.Dom.operand_dominates_op]
  have vNotOpLhs : ¬ lhs ∈ op.getResults! ctx.raw := by
    grind [IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates ctxDom (op₁ := op)]
  -- Source value: `op`'s result is `icmp lhs (constant c) pred`.
  rw [show op.getResults ctx.raw (by grind) = #[ValuePtr.opResult (op.getResult 0)] from by
    simp only [OperationPtr.getResults]
    rw [← OperationPtr.getNumResults!_eq_getNumResults (by grind), hNumResults,
      show Array.range 1 = #[0] from by decide]; simp]
    at hsourceValues
  simp at hsourceValues
  simp [hRes] at hsourceValues
  subst sourceValues
  -- Normalise `lt.bitwidth = 64`.
  obtain ⟨bw⟩ := lt
  have hbw : bw = 64 := by have hw : ¬ (bw ≠ 64) := hWidth64; omega
  subst hbw
  simp only at hlVal hRes hRhsType hrhsVal ⊢
  -- Result type is `i1`.
  have hResType : ((op.getResult 0).get! ctx.raw).type.val = Attribute.integerType ⟨1⟩ := by
    obtain ⟨w⟩ := it; simp only at hResBw; subst hResBw; exact hResIt
  -- Dispatch on the predicate.
  obtain ⟨pred⟩ := prop
  cases pred
  case eq => simp at hpattern
  case ne => simp at hpattern
  case ugt => simp at hpattern
  case sgt => simp at hpattern
  case slt =>
    split at hpattern
    case h_1 =>
      rename_i hpred
      sltiNonWrapArm Riscv.slti, Data.RISCV.slti, cst.value, slti_slt cst.value hLo hHi hxtRef
    all_goals first | (rename_i hd; exact absurd hd (by decide)) | exact absurd rfl (by assumption)
  case ult =>
    split at hpattern
    case h_2 =>
      rename_i hpred
      sltiNonWrapArm Riscv.sltiu, Data.RISCV.sltiu, cst.value, sltiu_ult cst.value hLo hHi hxtRef
    all_goals first | (rename_i hd; exact absurd hd (by decide)) | exact absurd rfl (by assumption)
  case sle =>
    split at hpattern
    case h_5 =>
      rename_i hpred
      sltiNonWrapArm Riscv.slti, Data.RISCV.slti, (cst.value + 1), slti_sle cst.value hLo hHi hxtRef
    all_goals first | (rename_i hd; exact absurd hd (by decide)) | exact absurd rfl (by assumption)
  case ule =>
    split at hpattern
    case h_6 =>
      rename_i hpred
      split at hpattern
      case isTrue h => simp at hpattern
      rename_i hc
      sltiNonWrapArm Riscv.sltiu, Data.RISCV.sltiu, (cst.value + 1),
        sltiu_ule cst.value hLo hHi hc hxtRef
    all_goals first | (rename_i hd; exact absurd hd (by decide)) | exact absurd rfl (by assumption)
  case sge =>
    split at hpattern
    case h_3 =>
      rename_i hpred
      sltiWrapArm Riscv.slti, Data.RISCV.slti, cst.value, slti_sge cst.value hLo hHi hxtRef
    all_goals first | (rename_i hd; exact absurd hd (by decide)) | exact absurd rfl (by assumption)
  case uge =>
    split at hpattern
    case h_4 =>
      rename_i hpred
      sltiWrapArm Riscv.sltiu, Data.RISCV.sltiu, cst.value, sltiu_uge cst.value hLo hHi hxtRef
    all_goals first | (rename_i hd; exact absurd hd (by decide)) | exact absurd rfl (by assumption)

/--
info: 'Veir.slti_local_preservesSemantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 floatEqOfToBitsEq,
 OperationPtr.dominates,
 OperationPtr.dominatesIp,
 OperationPtr.dominatesIp_before,
 OperationPtr.dominates_refl,
 OperationPtr.satisfyInvariants_of_IRContext_satisfyOpInvariants,
 OperationPtr.strictlyDominates_of_getDefiningOp!_of_mem_getOperands!,
 ValuePtr.dominatesIp,
 ValuePtr.dominatesIp_before_WfRewriter_createOp,
 IRContext.Dom.value_not_in_results_of_forall_in_operands_of_dominates,
 slti_sge._native.bv_decide.ax_1_8,
 slti_sle._native.bv_decide.ax_1_8,
 sltiu_uge._native.bv_decide.ax_1_8,
 sltiu_ule._native.bv_decide.ax_1_8,
 MemoryState.llvmLoad._native.bv_decide.ax_8]
-/
#guard_msgs in
#print axioms slti_local_preservesSemantics

end Veir
