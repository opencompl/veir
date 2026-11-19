module

public import Veir.Passes.Legalization.Validity.PhiSegments
public import Veir.Interfaces.ControlFlowInterfaces
public import Veir.Interpreter.Basic
import all Veir.Passes.Legalization.Validity.PhiSegments
import Veir.Dialects.GMIR.Lemmas
import all Veir.Dialects.Cf.OpInfo
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Dialects.RISCV_Cf.OpInfo
import all Veir.GlobalOpInfo
import all Veir.Interfaces.ControlFlowInterfaces

public section

namespace Veir.Legalization.CTreeProofs

/-- A successful run takes an edge whose forwarded arguments are exactly the segment reported
by the branch interface. Replacing the forwarded values keeps that edge and reads the same
segment from the new operands. -/
def ForwardsBranchSegment (code : OpCode) (props : propertiesOf code)
    (successors : Array BlockPtr) (fixed : Nat) (pointers : Array ValuePtr) : Prop :=
  ∀ (operands : Array RuntimeValue)
    (_ : pointers.size = operands.size) (mem : MemoryState)
    (resultTypes : Array TypeAttr) (results : Array RuntimeValue)
    (mem' : MemoryState) (action : Option ControlFlowAction),
    interpretOp' code props resultTypes operands successors mem = .ok (results, mem', action) →
    ∃ edge first last dest,
      successors[edge]? = some dest ∧
      ((OpCode.branchOpInterface? code).bind fun iface =>
        iface.getSuccessorOperandsImpl? props pointers edge) =
        some { beginOperandIndex := first, forwardedOperands := pointers.extract first last } ∧
      results = #[] ∧ mem' = mem ∧ action = some (.branch (operands.extract first last) dest) ∧
      ∀ (newOperands : Array RuntimeValue) (newMem : MemoryState),
        newOperands.size = operands.size →
        (∀ i < fixed, newOperands[i]? = operands[i]?) →
        interpretOp' code props resultTypes newOperands successors newMem =
          .ok (#[], newMem, some (.branch (newOperands.extract first last) dest))

/-- The branches that pass all their operands pass exactly the positions that phi widening rewrites. -/
theorem forwards_unconditional {code : OpCode}
    (kind : code = .cf .br ∨ code = .llvm .br ∨ code = .gmir .g_br ∨ code = .riscv_cf .branch)
    (props : propertiesOf code) (dest : BlockPtr) (pointers : Array ValuePtr) :
    ForwardsBranchSegment code props #[dest] 0 pointers := by
  intro operands sizes mem types results mem' action run
  refine ⟨0, 0, operands.size, dest, by simp, ?_, ?_⟩
  · rw [← sizes, Array.extract_size]
    rcases kind with rfl | rfl | rfl | rfl <;> rfl
  · have eq : ∀ (values : Array RuntimeValue) (memory : MemoryState),
        interpretOp' code props types values #[dest] memory =
          .ok (#[], memory, some (.branch values dest)) := by
      intro values memory
      rcases kind with rfl | rfl | rfl | rfl <;> rfl
    rw [eq] at run
    obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Interp.ok.inj run) |>.imp_right Prod.mk.inj
    simp only [Array.extract_size, true_and]
    intro values memory size _
    simpa only [← size, Array.extract_size] using eq values memory

/-- The segment of a conditional branch selected by its fixed operands. -/
private def conditionalAction (test : Bool) (values : Array RuntimeValue)
    (fixed firstCount : Nat) (yes no : BlockPtr) : ControlFlowAction :=
  if test then .branch (values.extract fixed (fixed + firstCount)) yes
  else .branch (values.extract (fixed + firstCount) values.size) no

/-- Relate the interpreter of a conditional branch to its segment interface once the fixed
operands have determined which successor it takes. -/
private theorem forwards_conditional {code : OpCode} {props : propertiesOf code}
    {yes no : BlockPtr} {pointers : Array ValuePtr} {fixed firstCount : Nat}
    (segments : ∀ edge : Nat, edge < 2 →
      ((OpCode.branchOpInterface? code).bind fun iface =>
        iface.getSuccessorOperandsImpl? props pointers edge) =
        (if edge = 0 then some ⟨pointers.extract fixed (fixed + firstCount), fixed⟩
          else some ⟨pointers.extract (fixed + firstCount) pointers.size, fixed + firstCount⟩))
    (read : Array RuntimeValue → Option Bool)
    (sameTest : ∀ {a b : Array RuntimeValue}, (∀ i < fixed, a[i]? = b[i]?) → read a = read b)
    (run_iff : ∀ values memory types results mem' action,
      interpretOp' code props types values #[yes, no] memory = .ok (results, mem', action) ↔
      ∃ test, read values = some test ∧ results = #[] ∧ mem' = memory ∧
        action = some (conditionalAction test values fixed firstCount yes no)) :
    ForwardsBranchSegment code props #[yes, no] fixed pointers := by
  intro values valuesSize memory types results mem' action run
  obtain ⟨test, readTest, rfl, rfl, rfl⟩ := (run_iff ..).mp run
  cases test with
  | false =>
    refine ⟨1, fixed + firstCount, pointers.size, no, rfl, by simpa using segments 1 (by decide),
      rfl, rfl, by simp [conditionalAction, valuesSize], ?_⟩
    intro target mem targetSize unchanged
    exact (run_iff ..).mpr ⟨false, (sameTest unchanged).trans readTest, rfl, rfl,
      by simp [conditionalAction, valuesSize, targetSize]⟩
  | true =>
    refine ⟨0, fixed, fixed + firstCount, yes, rfl, by simpa using segments 0 (by decide),
      rfl, rfl, rfl, ?_⟩
    intro target mem _ unchanged
    exact (run_iff ..).mpr ⟨true, (sameTest unchanged).trans readTest, rfl, rfl, rfl⟩

/-- The interface uses the same split between forwarded operand lists as the interpreter. -/
private theorem integerBranchSegments (pointers : Array ValuePtr) (yes no : Int)
    (size : pointers.size = 1 + yes.toNat + no.toNat) (edge : Nat) (valid : edge < 2) :
    BranchOpInterface.getSegmentedSuccessorOperands? 1 #[1, yes, no] pointers edge =
      (if edge = 0 then some ⟨pointers.extract 1 (1 + yes.toNat), 1⟩
       else some ⟨pointers.extract (1 + yes.toNat) pointers.size, 1 + yes.toNat⟩) := by
  obtain rfl | rfl : edge = 0 ∨ edge = 1 := by omega
  · rfl
  · rw [size]
    change some (SuccessorOperands.mk (pointers.extract (1 + (0 + yes.toNat)) (1 + (0 + yes.toNat) + no.toNat))
      (1 + (0 + yes.toNat))) = _
    simp

private def intBranchTest (value : Option RuntimeValue) : Option Bool :=
  match value with
  | some (.int _ (.val cond)) => some (decide (cond ≠ 0))
  | _ => none

/-- A gMIR conditional keeps its successor when only forwarded operands change. -/
theorem forwards_gmir_brcond (props : propertiesOf (OpCode.gmir .g_brcond))
    {yesCount noCount : Int} (sizes : props.operandSegmentSizes.values =
      #[1, yesCount, noCount])
    (yes no : BlockPtr) (pointers : Array ValuePtr)
    (size : pointers.size = 1 + yesCount.toNat + noCount.toNat) :
    ForwardsBranchSegment (.gmir .g_brcond) props #[yes, no] 1 pointers := by
  refine forwards_conditional (firstCount := yesCount.toNat) ?_ (fun a => intBranchTest a[0]?) ?_ ?_
  · intro edge valid
    change BranchOpInterface.getSegmentedSuccessorOperands? 1 props.operandSegmentSizes.values
      pointers edge = _
    rw [sizes]
    exact integerBranchSegments pointers yesCount noCount size edge valid
  · intro a b same
    rw [same 0 (by decide)]
  · intro values memory types results mem' action
    rw [interpretOp'_gmir_g_brcond_eq_ok_iff]
    constructor
    · rintro ⟨d, d', w, cond, count, dest, control, segment, rfl, rfl, rfl⟩
      obtain ⟨rfl, rfl⟩ : yes = d ∧ no = d' := by simpa using dest
      rw [sizes] at segment
      obtain rfl : yesCount = count := Option.some.inj segment
      refine ⟨decide (cond ≠ 0), by simp [intBranchTest, control], rfl, rfl, ?_⟩
      simp [conditionalAction, Nat.add_comm]
    · rintro ⟨test, control, rfl, rfl, rfl⟩
      unfold intBranchTest at control
      split at control <;> try contradiction
      next w cond h =>
        obtain rfl := Option.some.inj control
        exact ⟨yes, no, w, cond, yesCount, rfl, h, by rw [sizes]; rfl, rfl, rfl,
          by simp [conditionalAction, Nat.add_comm]⟩

private def i1BranchTest (value : Option RuntimeValue) : Option Bool :=
  match value with
  | some (.int 1 (.val cond)) => some (decide (cond = 1#1))
  | _ => none

/-- `cf.cond_br` and `llvm.cond_br` use the same one-bit condition and successor segments. -/
theorem forwards_i1_brcond {code : OpCode} (kind : code = .cf .cond_br ∨ code = .llvm .cond_br)
    (props : propertiesOf code) (yesCount noCount : Int)
    (sizes : (match code, props with
      | .cf .cond_br, p => p.operandSegmentSizes.values
      | .llvm .cond_br, p => p.operandSegmentSizes.values
      | _, _ => #[]) = #[1, yesCount, noCount])
    (yes no : BlockPtr) (pointers : Array ValuePtr)
    (size : pointers.size = 1 + yesCount.toNat + noCount.toNat) :
    ForwardsBranchSegment code props #[yes, no] 1 pointers := by
  refine forwards_conditional (firstCount := yesCount.toNat) ?_ (fun a => i1BranchTest a[0]?) ?_ ?_
  · intro edge valid
    rcases kind with rfl | rfl <;>
      change BranchOpInterface.getSegmentedSuccessorOperands? 1 props.operandSegmentSizes.values
        pointers edge = _ <;> rw [show props.operandSegmentSizes.values = _ from sizes] <;>
      exact integerBranchSegments pointers yesCount noCount size edge valid
  · intro a b same
    rw [same 0 (by decide)]
  · intro values memory types results mem' action
    rcases kind with rfl | rfl
    all_goals
      have count : props.operandSegmentSizes.values[1]? = some (↑yesCount : Int) := by
        rw [show props.operandSegmentSizes.values = _ from sizes]; rfl
      cases control : values[0]? with
      | none => simp [interpretOp', Cf.interpretOp', Llvm.interpretOp', control, i1BranchTest]
      | some value =>
        cases value with
        | int w x =>
          cases w with
          | zero => simp [interpretOp', Cf.interpretOp', Llvm.interpretOp', control, count, i1BranchTest]
          | succ n =>
            cases n with
            | zero =>
              cases x <;> simp [interpretOp', Cf.interpretOp', Llvm.interpretOp', control, count,
                i1BranchTest, conditionalAction, Nat.add_comm, bind, pure]
              split <;> grind
            | succ n => simp [interpretOp', Cf.interpretOp', Llvm.interpretOp', control, count, i1BranchTest]
        | _ => simp [interpretOp', Cf.interpretOp', Llvm.interpretOp', control, count, i1BranchTest]

/-- CIR branches expose successor operands to the rewriter. Their interpreter has no successful
branch action. -/
theorem forwards_cir {op : Cir} (kind : op = .br ∨ op = .brcond) (props : propertiesOf (OpCode.cir op))
    (successors : Array BlockPtr) (fixed : Nat) (pointers : Array ValuePtr) :
    ForwardsBranchSegment (.cir op) props successors fixed pointers := by
  intro _ _ _ _ _ _ _ run
  rcases kind with rfl | rfl <;> contradiction

private abbrev BranchOutcome := Array RuntimeValue × MemoryState × Option ControlFlowAction

private def switchStep (counts : Array Int) (bits : Array Nat) (key : Nat)
    (succs : Array BlockPtr) (values : Array RuntimeValue) (memory : MemoryState)
    (i : Nat) (state : Option BranchOutcome × Nat) : Interp (ForInStep (Option BranchOutcome × Nat)) :=
  match counts[i]? with
  | some count =>
    if key = bits[i]! then
      match succs[i + 1]? with
      | some dest => .ok (.done (some (#[], memory, some (.branch
          (values.extract state.2 (state.2 + count.toNat)) dest)), state.2))
      | none => .fail none
    else .ok (.yield (none, state.2 + count.toNat))
  | none => .fail none

private def switchCases (counts : Array Int) (bits : Array Nat) (key : Nat)
    (succs : Array BlockPtr) (defaultDest : BlockPtr) (defaultCount : Int) (first n base : Nat)
    (values : Array RuntimeValue) (memory : MemoryState) : Interp BranchOutcome := do
  let state ← forIn (List.range' first n) (none, base) (switchStep counts bits key succs values memory)
  match state.1 with
  | some r => pure r
  | none => pure (#[], memory, some (.branch (values.extract 1 (1 + defaultCount.toNat)) defaultDest))

private theorem switchCases_forwards (counts : Array Int) (bits : Array Nat) (key : Nat)
    (succs : Array BlockPtr) (defaultDest : BlockPtr) (defaultCount : Int)
    (pointers : Array ValuePtr) (hd : succs[0]? = some defaultDest)
    (size : succs.size = counts.size + 1) {first n : Nat} (bound : first + n ≤ counts.size) :
    let sizes := #[1, defaultCount] ++ counts
    ∃ edge start stop dest, succs[edge]? = some dest ∧
      BranchOpInterface.getSegmentedSuccessorOperands? 1 sizes pointers edge =
        some ⟨pointers.extract start stop, start⟩ ∧
      ∀ values memory, switchCases counts bits key succs defaultDest defaultCount first n
          (successorSegmentStart 1 sizes (first + 1)) values memory =
        .ok (#[], memory, some (.branch (values.extract start stop) dest)) := by
  dsimp only
  induction n generalizing first with
  | zero =>
    refine ⟨0, 1, 1 + defaultCount.toNat, defaultDest, hd, ?_, fun _ _ => rfl⟩
    simp [BranchOpInterface.getSegmentedSuccessorOperands?, Array.getElem?_append]
  | succ n ih =>
    let sizes := #[1, defaultCount] ++ counts
    have inBounds : first < counts.size := by omega
    let count := counts[first]
    have hCount : counts[first]? = some count := by simp [count]
    have hSize : sizes[1 + (first + 1)]? = some count := by
      simp [sizes, Array.getElem?_append, count, inBounds, Nat.add_comm 1]
    let start := successorSegmentStart 1 sizes (first + 1)
    by_cases hit : key = bits[first]!
    · have destIn : first + 1 < succs.size := by omega
      let dest := succs[first + 1]
      have hDest : succs[first + 1]? = some dest := by simp [dest, destIn]
      refine ⟨first + 1, start, start + count.toNat, dest, hDest, ?_, fun values memory => ?_⟩
      · change BranchOpInterface.getSegmentedSuccessorOperands? 1 sizes pointers (first + 1) = _
        simp [BranchOpInterface.getSegmentedSuccessorOperands?, hSize, start, successorSegmentStart]
      · simp [switchCases, List.range'_succ, switchStep, hCount, hit, hDest, start, sizes,
          Pure.pure, Bind.bind]
    · obtain ⟨edge, off, stop, dest, hDest, hSeg, hLoop⟩ := ih (first := first + 1) (by omega)
      refine ⟨edge, off, stop, dest, hDest, hSeg, fun values memory => ?_⟩
      have next := segmentStart_succ (fixed := 1) (i := first + 1) hSize
      simpa [switchCases, List.range'_succ, switchStep, hCount, hit, start, sizes, next,
        Pure.pure, Bind.bind] using hLoop values memory

private theorem interpretSwitch_eq {props : propertiesOf (OpCode.llvm .switch)}
    {values : Array RuntimeValue} {succs : Array BlockPtr} {d : BlockPtr} {w : Nat}
    {x : BitVec w} {defaultCount : Int} {cases : LLVMSwitchCaseValues}
    (hd : succs[0]? = some d) (hv : values[0]? = some (.int w (.val x)))
    (hn : props.operandSegmentSizes.values[1]? = some defaultCount)
    (hk : props.caseValues? w = some cases) (types : Array TypeAttr) (mem : MemoryState) :
    interpretOp' (.llvm .switch) props types values succs mem =
      switchCases props.case_operand_segments.values cases.bits x.toNat succs d defaultCount
        0 props.case_operand_segments.values.size (1 + defaultCount.toNat) values mem := by
  simp only [interpretOp', Llvm.interpretOp', hd, hv, hn, hk, Std.Legacy.Range.forIn_eq_forIn_range',
    switchCases, Std.Legacy.Range.size]
  simp only [Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  congr 1
  congr 1
  funext i state
  unfold switchStep
  cases props.case_operand_segments.values[i]? with
  | none => rfl
  | some count =>
    by_cases hit : x.toNat = cases.bits[i]!
    · simp only [hit, ↓reduceIte]
      cases succs[i + 1]? <;> rfl
    · simp only [hit, ↓reduceIte]; rfl
  funext state
  cases state.1 <;> rfl

/-- A switch chooses the same case on both runs. Its forwarded operand offset is the sum of the
default argument count and the preceding case argument counts, plus the position of the key. -/
theorem forwards_llvm_switch (props : propertiesOf (OpCode.llvm .switch))
    (succs : Array BlockPtr) (size : succs.size = props.case_operand_segments.values.size + 1)
    (pointers : Array ValuePtr) : ForwardsBranchSegment (.llvm .switch) props succs 1 pointers := by
  intro values _ mem types results mem' action run
  have first : 0 < succs.size := by omega
  let d := succs[0]
  have hd : succs[0]? = some d := by simp [d, first]
  cases hn : props.operandSegmentSizes.values[1]? with
  | none =>
    simp only [interpretOp', Llvm.interpretOp', hd, hn] at run
    split at run <;> contradiction
  | some defaultCount =>
    cases hv : values[0]? with
    | none => simp [interpretOp', Llvm.interpretOp', hd, hv] at run
    | some val =>
      cases val with
      | int w v =>
        cases v with
        | poison => simp [interpretOp', Llvm.interpretOp', hd, hv, hn] at run
        | val x =>
          cases hk : props.caseValues? w with
          | none => simp [interpretOp', Llvm.interpretOp', hd, hv, hn, hk] at run
          | some cases =>
            obtain ⟨edge, start, stop, dest, hDest, segment, runs⟩ :=
              switchCases_forwards props.case_operand_segments.values cases.bits x.toNat
                succs d defaultCount pointers hd size (first := 0) (n := props.case_operand_segments.values.size) (by simp)
            have off : successorSegmentStart 1 (#[1, defaultCount] ++ props.case_operand_segments.values) 1 =
                1 + defaultCount.toNat := by
              simp [successorSegmentStart, Array.extract_append]
            rw [off] at runs
            rw [interpretSwitch_eq hd hv hn hk, runs] at run
            obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.inj (Interp.ok.inj run) |>.imp_right Prod.mk.inj
            refine ⟨edge, start, stop, dest, hDest, ?_, rfl, rfl, rfl, ?_⟩
            · change Llvm.getSwitchSuccessorOperands? props pointers edge = _
              simpa [Llvm.getSwitchSuccessorOperands?, hn] using segment
            · intro target memory _ same
              exact (interpretSwitch_eq hd ((same 0 (by decide)).trans hv) hn hk types memory).trans
                (runs target memory)
      | _ => simp [interpretOp', Llvm.interpretOp', hd, hv, hn] at run

/-- The fixed operand count and segment sizes of a conditional RISC-V branch. -/
def riscvBranchSegments (op : Riscv_Cf) (props : propertiesOf (OpCode.riscv_cf op)) :
    Option (Nat × Array Int) :=
  match op with
  | .beqz | .bnez => some (1, props.operandSegmentSizes.values)
  | .beq | .bne | .blt | .bge | .bltu | .bgeu => some (2, props.operandSegmentSizes.values)
  | _ => none

private theorem compareBranchSegments (pointers : Array ValuePtr) (yes no : Int)
    (size : pointers.size = 2 + yes.toNat + no.toNat) (edge : Nat) (valid : edge < 2) :
    BranchOpInterface.getSegmentedSuccessorOperands? 2 #[1, 1, yes, no] pointers edge =
      (if edge = 0 then some ⟨pointers.extract 2 (2 + yes.toNat), 2⟩
       else some ⟨pointers.extract (2 + yes.toNat) pointers.size, 2 + yes.toNat⟩) := by
  obtain rfl | rfl : edge = 0 ∨ edge = 1 := by omega
  · rfl
  · rw [size]
    change some (SuccessorOperands.mk (pointers.extract (2 + (0 + yes.toNat)) (2 + (0 + yes.toNat) + no.toNat))
      (2 + (0 + yes.toNat))) = _
    simp

private def riscvBranchTest (op : Riscv_Cf) (a b : Option RuntimeValue) : Option Bool := do
  let some (.reg lhs) := a | none
  match op with
  | .beqz => return lhs.val = 0#64
  | .bnez => return lhs.val ≠ 0#64
  | _ =>
    let some (.reg rhs) := b | none
    match op with
    | .beq => return lhs == rhs
    | .bne => return lhs != rhs
    | .blt => return lhs.val.slt rhs.val
    | .bge => return !lhs.val.slt rhs.val
    | .bltu => return lhs.val.ult rhs.val
    | .bgeu => return !lhs.val.ult rhs.val
    | _ => none

/-- RISC-V compare-and-branch and branch-on-zero select their successor from the fixed registers. -/
theorem forwards_riscv_conditional (op : Riscv_Cf) (props : propertiesOf (OpCode.riscv_cf op))
    {fixed : Nat} {yesCount noCount : Int} (yes no : BlockPtr) (pointers : Array ValuePtr)
    (size : pointers.size = fixed + yesCount.toNat + noCount.toNat)
    (shape : riscvBranchSegments op props =
      some (fixed, Array.replicate fixed 1 ++ #[yesCount, noCount])) :
    ForwardsBranchSegment (.riscv_cf op) props #[yes, no] fixed pointers := by
  refine forwards_conditional (firstCount := yesCount.toNat) ?_
    (fun a => riscvBranchTest op a[0]? a[1]?) ?_ ?_
  · intro edge valid
    cases op <;> simp only [riscvBranchSegments, Option.some.injEq, Prod.mk.injEq] at shape
    all_goals first | contradiction | obtain ⟨rfl, sizes⟩ := shape
    all_goals first
      | (change BranchOpInterface.getSegmentedSuccessorOperands? 1 props.operandSegmentSizes.values
            pointers edge = _
         rw [sizes]
         exact integerBranchSegments pointers yesCount noCount size edge valid)
      | (change BranchOpInterface.getSegmentedSuccessorOperands? 2 props.operandSegmentSizes.values
            pointers edge = _
         rw [sizes]
         exact compareBranchSegments pointers yesCount noCount size edge valid)
  · intro a b same
    cases op <;> simp only [riscvBranchSegments, Option.some.injEq, Prod.mk.injEq] at shape
    all_goals first | contradiction | obtain ⟨rfl, _⟩ := shape
    all_goals rw [same 0 (by decide)]
    all_goals first | rw [same 1 (by decide)] | cases b[0]? <;> rfl
  · intro vals mem types results mem' action
    cases op <;> simp only [riscvBranchSegments, Option.some.injEq, Prod.mk.injEq] at shape
    all_goals first | contradiction | obtain ⟨rfl, sizes⟩ := shape
    all_goals first
      | have count : props.operandSegmentSizes.values[1]? = some yesCount := by rw [sizes]; rfl
      | have count : props.operandSegmentSizes.values[2]? = some yesCount := by rw [sizes]; rfl
    all_goals clear sizes
    all_goals simp only [interpretOp', Riscv_Cf.interpretOp', count, riscvBranchTest]
    all_goals cases h₀ : vals[0]? <;> simp [conditionalAction, bind, pure, Nat.add_comm]
    all_goals rename_i v
    all_goals cases v <;> simp
    all_goals first
      | (split <;> simp <;> grind; done)
      | skip
    all_goals cases h₁ : vals[1]? <;> simp [conditionalAction, bind, pure, Nat.add_comm]
    all_goals rename_i v
    all_goals cases v <;> simp
    all_goals split <;> rename_i test <;> simp [test] <;> grind

end Veir.Legalization.CTreeProofs
