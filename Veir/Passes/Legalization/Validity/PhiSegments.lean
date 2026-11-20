module

public import Veir.Interfaces.ControlFlowInterfaces
public import Veir.Interpreter.ResultsConformLemmas
import all Veir.Interfaces.ControlFlowInterfaces
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Verifier.Basic
import all Veir.IR.Basic
import all Veir.IR.Attribute
import all Veir.IR.OpInfo

public section

namespace Veir.Legalization.CTreeProofs

/-- The control operands before the forwarded successor segments. -/
def phiBranchFixedOperands : OpCode → Nat
  | .riscv_cf .beq | .riscv_cf .bne | .riscv_cf .blt | .riscv_cf .bge
  | .riscv_cf .bltu | .riscv_cf .bgeu => 2
  | .riscv_cf .beqz | .riscv_cf .bnez | .cf .cond_br | .llvm .cond_br | .llvm .switch
  | .gmir .g_brcond | .cir .brcond => 1
  | _ => 0

/-- A selected argument of integer type has the same type as its verified incoming operand. -/
theorem verifyBranchSuccessorArgTypes_integer {ctx : WfIRContext OpCode} {op : OperationPtr}
    {dest : BlockPtr} {base i : Nat} {msg : String} {t : IntegerType}
    (valid : op.verifyBranchSuccessorArgTypes ctx base dest msg = .ok ())
    (bound : i < dest.getNumArguments! ctx.raw)
    (argType : (dest.getArgument i).getType! ctx.raw = (t : TypeAttr)) :
    (op.getOperand! ctx.raw (base + i)).getType! ctx.raw = (t : TypeAttr) := by
  unfold OperationPtr.verifyBranchSuccessorArgTypes at valid
  have compatible := Except.forIn_range_ok
    (fun j => Attribute.branchArgCompatible
      ((op.getOperand! ctx.raw (base + j)).getType! ctx.raw).val
      ((dest.getArgument j).getType! ctx.raw).val = true)
    (h := bind_ok_left valid) (fun j s hs => by
      dsimp only at hs
      split at hs
      · contradiction
      · exact ⟨Except.ok.inj hs.symm, by cases b : Attribute.branchArgCompatible _ _ <;> simp_all⟩) i bound
  rw [argType] at compatible
  apply Subtype.ext
  have check (x : Attribute) : x.branchArgCompatible (.integerType t) = decide (x = .integerType t) := by
    cases x <;> rfl
  exact of_decide_eq_true ((check _).symm.trans compatible)

/-- The offset of the first forwarded operand on the given edge of a segmented branch. -/
def successorSegmentStart (fixed : Nat) (sizes : Array Int) (edge : Nat) :=
  fixed + (sizes.extract fixed (fixed + edge)).foldl (fun n s => n + s.toNat) 0

theorem segmentedSuccessorOperands_spec {fixed edge : Nat} {sizes : Array Int}
    {values : Array ValuePtr} {segment : SuccessorOperands}
    (run : BranchOpInterface.getSegmentedSuccessorOperands? fixed sizes values edge = some segment) :
    ∃ count, sizes[fixed + edge]? = some count ∧
      segment.beginOperandIndex = successorSegmentStart fixed sizes edge ∧
      segment.forwardedOperands = values.extract segment.beginOperandIndex
        (segment.beginOperandIndex + count.toNat) := by
  unfold BranchOpInterface.getSegmentedSuccessorOperands? at run
  simp only [bind, Option.bind] at run
  split at run <;> try contradiction
  rename_i count h
  cases run
  exact ⟨count, h, rfl, rfl⟩

private theorem foldWidths_ge (sizes : Array Int) (n : Nat) :
    n ≤ sizes.foldl (fun a s => a + s.toNat) n := by
  rw [← Array.foldl_toList]
  induction sizes.toList generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_add_right _ _) (ih _)

private theorem segmentStart_mono {fixed i j : Nat} {sizes : Array Int} (h : i ≤ j) :
    successorSegmentStart fixed sizes i ≤ successorSegmentStart fixed sizes j := by
  have split := Array.extract_append_extract (as := sizes) (i := fixed)
    (j := fixed + i) (k := fixed + j)
  rw [Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)] at split
  unfold successorSegmentStart
  rw [← split, Array.foldl_append]
  exact Nat.add_le_add_left (foldWidths_ge _ _) _

theorem segmentStart_succ {fixed i : Nat} {sizes : Array Int} {count : Int}
    (hc : sizes[fixed + i]? = some count) :
    successorSegmentStart fixed sizes (i + 1) = successorSegmentStart fixed sizes i + count.toNat := by
  obtain ⟨bound, val⟩ := Array.getElem?_eq_some_iff.mp hc
  have split := Array.extract_append_extract (as := sizes) (i := fixed)
    (j := fixed + i) (k := fixed + (i + 1))
  rw [Nat.min_eq_left (by omega), Nat.max_eq_right (by omega)] at split
  have singleton : sizes.extract (fixed+i) (fixed+(i+1)) = #[count] := by
    apply Array.ext
    · simp [Array.size_extract]; omega
    · intro j h₁ h₂
      have : j = 0 := by simpa using h₂
      subst j
      simpa [Array.getElem_extract] using val
  unfold successorSegmentStart
  rw [← split, singleton, Array.foldl_append]
  simp [Nat.add_assoc]

/-- Distinct successor segments of one branch cannot refer to the same forwarded operand slot. -/
theorem segmentedSuccessorOperands_disjoint {fixed i j ai aj : Nat} {sizes : Array Int}
    {values : Array ValuePtr} {s t : SuccessorOperands} (order : i < j)
    (si : BranchOpInterface.getSegmentedSuccessorOperands? fixed sizes values i = some s)
    (sj : BranchOpInterface.getSegmentedSuccessorOperands? fixed sizes values j = some t)
    (hi : ai < s.forwardedOperands.size) :
    s.getOperandIndex ai < t.getOperandIndex aj := by
  obtain ⟨c, hc, hs, hv⟩ := segmentedSuccessorOperands_spec si
  obtain ⟨_, _, ht, _⟩ := segmentedSuccessorOperands_spec sj
  have h := segmentStart_mono (sizes := sizes) (fixed := fixed) (i := i + 1) (j := j) order
  rw [segmentStart_succ hc] at h
  rw [hv, Array.size_extract] at hi
  simp only [SuccessorOperands.getOperandIndex, hs, ht]
  omega

/-- The verified segment contains one slot per destination argument, and its slots forward values
of the original integer types of any selected destination arguments. -/
structure VerifiedPhiSegment (ctx : WfIRContext OpCode) (branch : OperationPtr)
    (dest : BlockPtr) (segment : SuccessorOperands) : Prop where
  count : segment.forwardedOperands.size = dest.getNumArguments! ctx.raw
  limit : segment.beginOperandIndex + dest.getNumArguments! ctx.raw ≤ branch.getNumOperands! ctx.raw
  integerType : ∀ {i t}, i < dest.getNumArguments! ctx.raw →
    (dest.getArgument i).getType! ctx.raw = (t : IntegerType) →
    (branch.getOperand! ctx.raw (segment.getOperandIndex i)).getType! ctx.raw = (t : TypeAttr)

theorem VerifiedPhiSegment.unconditional {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw}
    (valid : branch.verifyUnconditionalBranch ctx bp = .ok ()) :
    VerifiedPhiSegment ctx branch (branch.getSuccessor! ctx.raw 0)
      {forwardedOperands := branch.getOperands! ctx.raw} := by
  unfold OperationPtr.verifyUnconditionalBranch at valid
  have check := Except.ok_of_bind_ok valid
  dsimp only at check
  split at check <;> try contradiction
  rename_i hCount
  have count : branch.getNumOperands! ctx.raw = (branch.getSuccessor! ctx.raw 0).getNumArguments! ctx.raw := by grind
  exact ⟨by simpa using count, by simp [count], fun hi ht =>
    verifyBranchSuccessorArgTypes_integer check hi ht⟩

/-- A verifier loop that appends the nonnegative sizes faithfully records their natural values. -/
private theorem collectSizes {xs : Array Int} {acc out : Array Nat}
    {f : Int → Array Nat → Except String (ForInStep (Array Nat))}
    (ok : ∀ x a s, f x a = .ok s → s = .yield (a.push x.toNat))
    (run : forIn xs acc f = .ok out) : out = acc ++ xs.map Int.toNat := by
  rw [← Array.forIn_toList] at run
  suffices loop : ∀ (items : List Int) (init : Array Nat),
      forIn items init f = .ok out → out = init ++ (items.map Int.toNat).toArray by
    simpa only [← Array.toList_map, Array.toArray_toList] using loop xs.toList acc run
  intro items
  induction items with
  | nil => intro a h; simpa [pure, Except.pure] using h.symm
  | cons x items ih =>
    intro a h
    rw [List.forIn_cons] at h
    cases head : f x a with
    | error e => simp [head, bind, Except.bind] at h
    | ok s =>
      rw [ok x a s head] at head
      simp only [head, bind, Except.bind] at h
      rw [ih _ h]
      apply Array.toList_inj.mp
      simp

private theorem verifyCond_sizes {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} {sizes : DenseArrayAttr} {fixed : Nat}
    (valid : branch.verifyCondBranchOperandSegmentSizes ctx bp sizes fixed = .ok ()) :
    let counts := sizes.values.map Int.toNat
    counts.size = fixed + 2 ∧
    (∀ i < fixed, counts[i]! = 1) ∧
    counts.foldl (· + ·) 0 = branch.getNumOperands! ctx.raw ∧
    counts[fixed]! = (branch.getSuccessor! ctx.raw 0).getNumArguments! ctx.raw ∧
    counts[fixed + 1]! = (branch.getSuccessor! ctx.raw 1).getNumArguments! ctx.raw ∧
    (∃ msg, branch.verifyBranchSuccessorArgTypes ctx fixed (branch.getSuccessor! ctx.raw 0) msg = .ok ()) ∧
    ∃ msg, branch.verifyBranchSuccessorArgTypes ctx (fixed + counts[fixed]!) (branch.getSuccessor! ctx.raw 1) msg = .ok () := by
  unfold OperationPtr.verifyCondBranchOperandSegmentSizes at valid
  split at valid <;> try contradiction
  rename_i size
  obtain ⟨counts, read, rest⟩ := Except.bind_eq_ok.mp valid
  have hCounts := collectSizes (f := _) (run := read) (by
    intro x a s h
    dsimp only at h
    split at h <;> first | contradiction | exact Except.ok.inj h.symm)
  simp only [Array.empty_append] at hCounts
  subst counts
  have fixedOkay := Except.forIn_range_ok (fun i => (sizes.values.map Int.toNat)[i]! = 1)
    (h := bind_ok_left rest) (by
      intro i s h
      split at h <;> first | contradiction | exact ⟨Except.ok.inj h.symm, Classical.not_not.mp ‹¬ _›⟩)
  have rest := Except.ok_of_bind_ok rest
  dsimp only at rest
  split at rest <;> try contradiction
  split at rest <;> try contradiction
  split at rest <;> try contradiction
  exact ⟨by simpa using size, fixedOkay, by grind, by grind, by grind,
    ⟨_, bind_ok_left rest⟩, ⟨_, Except.ok_of_bind_ok rest⟩⟩

private theorem conditionalOperandCount {counts : Array Nat} {fixed : Nat}
    (fixedCount : fixed = 1 ∨ fixed = 2) (count : counts.size = fixed + 2)
    (prefixCount : ∀ i < fixed, counts[i]! = 1) :
    counts.foldl (· + ·) 0 = fixed + counts[fixed]! + counts[fixed + 1]! := by
  rcases fixedCount with rfl | rfl
  · have eq : counts = #[1, counts[1]!, counts[2]!] := by
      apply Array.ext (by simpa using count)
      intro i hi _
      have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rw [← getElem!_pos counts i hi]
      rcases this with rfl | rfl | rfl <;> simp [prefixCount]
    rw [eq]
    rfl
  · have eq : counts = #[1, 1, counts[2]!, counts[3]!] := by
      apply Array.ext (by simpa using count)
      intro i hi _
      have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rw [← getElem!_pos counts i hi]
      rcases this with rfl | rfl | rfl | rfl <;> simp [prefixCount]
    rw [eq]
    rfl

/-- The operand array of a checked conditional branch is partitioned into its fixed prefix
and two successor segments. -/
theorem conditionalSegmentCounts {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} {sizes : DenseArrayAttr} {fixed : Nat}
    (fixedCount : fixed = 1 ∨ fixed = 2)
    (valid : branch.verifyCondBranchOperandSegmentSizes ctx bp sizes fixed = .ok ()) :
    ∃ yes no : Int, sizes.values = Array.replicate fixed 1 ++ #[yes, no] ∧
      (branch.getOperands! ctx.raw).size = fixed + yes.toNat + no.toNat := by
  obtain ⟨length, ones, total, _⟩ := verifyCond_sizes valid
  have n : sizes.values.size = fixed + 2 := by simpa using length
  have getCount {i : Nat} (hi : i < sizes.values.size) :
      (sizes.values.map Int.toNat)[i]! = sizes.values[i].toNat := by
    simp [getElem!_pos (sizes.values.map Int.toNat) i (by simpa using hi)]
  refine ⟨sizes.values[fixed]'(by omega), sizes.values[fixed+1]'(by omega), ?_, ?_⟩
  · apply Array.ext (by simp [n])
    intro i hi hj
    by_cases before : i < fixed
    · have := ones i before
      rw [getCount hi] at this
      simp [before]
      omega
    · have : i = fixed ∨ i = fixed + 1 := by omega
      rcases this with rfl | rfl <;> simp
  · have h := (conditionalOperandCount fixedCount length ones).symm.trans total
    rw [getCount (by omega : fixed < sizes.values.size),
      getCount (by omega : fixed+1 < sizes.values.size)] at h
    simpa using h.symm

/-- The segment returned by any verified conditional branch has the checked bounds and types,
including when both successor operands name the same block. -/
theorem VerifiedPhiSegment.conditional {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} {fixed edge : Nat} {sizes : DenseArrayAttr} {s : SuccessorOperands}
    (fixedCount : fixed = 1 ∨ fixed = 2)
    (valid : branch.verifyCondBranchOperandSegmentSizes ctx bp sizes fixed = .ok ())
    (run : BranchOpInterface.getSegmentedSuccessorOperands? fixed sizes.values
      (branch.getOperands! ctx.raw) edge = some s) :
    VerifiedPhiSegment ctx branch (branch.getSuccessor! ctx.raw edge) s := by
  obtain ⟨size, fixedOnes, total, trueSize, falseSize, ⟨tm, trueTypes⟩, ⟨fm, falseTypes⟩⟩ :=
    verifyCond_sizes valid
  have operandCount := (conditionalOperandCount fixedCount size fixedOnes).symm.trans total
  obtain ⟨count, hc, start, array⟩ := segmentedSuccessorOperands_spec run
  obtain ⟨idx, hc'⟩ := Array.getElem?_eq_some_iff.mp hc
  have srcSize : sizes.values.size = fixed + 2 := by simpa using size
  have mapCount {j : Nat} (hj : j < sizes.values.size) :
      (sizes.values.map Int.toNat)[j]! = sizes.values[j].toNat := by
    simp [getElem!_pos (sizes.values.map Int.toNat) j (by simpa using hj)]
  have hzero : successorSegmentStart fixed sizes.values 0 = fixed := by
    have empty : sizes.values.extract fixed fixed = #[] := Array.ext (by simp; omega) (by simp)
    simp [successorSegmentStart, empty]
  have hc0 : fixed < sizes.values.size := by omega
  have hone := segmentStart_succ (fixed := fixed) (i := 0) (sizes := sizes.values)
    (count := sizes.values[fixed]) (by simp [hc0])
  simp only [hzero] at hone
  have options : edge = 0 ∨ edge = 1 := by omega
  rcases options with rfl | rfl
  · rw [hzero] at start
    have destCount : count.toNat = (branch.getSuccessor! ctx.raw 0).getNumArguments! ctx.raw := by
      rw [← hc', ← mapCount idx]
      simpa using trueSize
    have lim : s.beginOperandIndex + (branch.getSuccessor! ctx.raw 0).getNumArguments! ctx.raw ≤
        branch.getNumOperands! ctx.raw := by omega
    refine ⟨?_, lim, fun hi ht => ?_⟩
    · rw [array, Array.size_extract, destCount]
      have sizeOps := OperationPtr.getOperands!.size_eq_getNumOperands! (op := branch) (ctx := ctx.raw)
      omega
    · simpa only [SuccessorOperands.getOperandIndex, start] using
        verifyBranchSuccessorArgTypes_integer trueTypes hi ht
  · have destCount : count.toNat = (branch.getSuccessor! ctx.raw 1).getNumArguments! ctx.raw := by
      rw [← hc', ← mapCount idx]
      exact falseSize
    have base : s.beginOperandIndex = fixed + (sizes.values.map Int.toNat)[fixed]! := by
      rw [start, hone, mapCount hc0]
    have lim : s.beginOperandIndex + (branch.getSuccessor! ctx.raw 1).getNumArguments! ctx.raw ≤
        branch.getNumOperands! ctx.raw := by omega
    refine ⟨?_, lim, fun hi ht => ?_⟩
    · rw [array, Array.size_extract, destCount]
      have sizeOps := OperationPtr.getOperands!.size_eq_getNumOperands! (op := branch) (ctx := ctx.raw)
      omega
    · simpa only [SuccessorOperands.getOperandIndex, base] using
        verifyBranchSuccessorArgTypes_integer falseTypes hi ht

private theorem verifyOperandSegmentSizes_spec {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} {sizes : DenseArrayAttr} {expected : Nat} {out : Array Nat}
    (h : branch.verifyOperandSegmentSizes ctx bp sizes expected = .ok out) :
    out = sizes.values.map Int.toNat ∧ out.size = expected ∧
      out.foldl (· + ·) 0 = branch.getNumOperands! ctx.raw := by
  unfold OperationPtr.verifyOperandSegmentSizes at h
  dsimp only at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  obtain ⟨counts, read, rest⟩ := Except.bind_eq_ok.mp h
  have hCounts := collectSizes (run := read) (by
    intro x a s h
    split at h <;> first | contradiction | exact Except.ok.inj h.symm)
  simp only [Array.empty_append] at hCounts
  split at rest <;> try contradiction
  cases rest
  exact ⟨hCounts, by simp [hCounts]; omega, by grind⟩

private theorem rangeCountLoop {ε : Type} {f : Nat → Nat → Except ε (ForInStep Nat)}
    (n : Nat) (base : Nat → Nat) (P : Nat → Prop)
    (step : ∀ i < n, ∀ s, f i (base i) = .ok s → s = .yield (base (i + 1)) ∧ P i)
    {last : Nat} (h : forIn [0:n] (base 0) f = .ok last) :
    last = base n ∧ ∀ i < n, P i := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  suffices loop : ∀ i k, i + k = n → forIn (List.range' i k) (base i) f = .ok last →
      last = base n ∧ ∀ j, i ≤ j → j < n → P j by
    obtain ⟨endEq, holds⟩ := loop 0 n (by simp) (by simpa using h)
    exact ⟨endEq, fun j => holds j (by omega)⟩
  intro i k
  induction k generalizing i with
  | zero =>
    intro hi run
    simp only [Nat.add_zero] at hi
    simp [pure, Except.pure] at run
    exact ⟨hi ▸ run.symm, by omega⟩
  | succ k ih =>
    intro hi run
    rw [List.range'_succ, List.forIn_cons] at run
    cases hx : f i (base i) with
    | error e => simp [hx, bind, Except.bind] at run
    | ok s =>
      obtain ⟨rfl, prop⟩ := step i (by omega) _ hx
      simp only [hx, bind, Except.bind] at run
      obtain ⟨endEq, rest⟩ := ih (i + 1) (by omega) run
      exact ⟨endEq, fun j lo hj => by
        by_cases eq : j = i
        · simpa [eq] using prop
        · exact rest j (by omega) hj⟩

set_option maxHeartbeats 3000000 in
theorem VerifiedPhiSegment.llvmSwitch {ctx : WfIRContext OpCode} {branch : OperationPtr}
    {bp : branch.InBounds ctx.raw} {edge : Nat} {s : SuccessorOperands}
    (valid : Llvm.verifyLocalInvariants Llvm.switch branch ctx bp = .ok ())
    {defaultCount : Int}
    (hDefault : (branch.getProperties! ctx.raw Llvm.switch).operandSegmentSizes.values[1]? = some defaultCount)
    (run : BranchOpInterface.getSegmentedSuccessorOperands? 1
      (#[1, defaultCount] ++ (branch.getProperties! ctx.raw Llvm.switch).case_operand_segments.values)
      (branch.getOperands! ctx.raw) edge = some s) :
    VerifiedPhiSegment ctx branch (branch.getSuccessor! ctx.raw edge) s := by
  let props := branch.getProperties! ctx.raw Llvm.switch
  let sizes : Array Int := #[1, defaultCount] ++ props.case_operand_segments.values
  change BranchOpInterface.getSegmentedSuccessorOperands? 1 sizes _ edge = some s at run
  unfold Llvm.verifyLocalInvariants at valid
  replace valid := Except.ok_of_bind_ok valid
  dsimp only at valid
  replace valid := Except.ok_of_bind_ok valid
  obtain ⟨counts, getCounts, rest⟩ := Except.bind_eq_ok.mp valid
  clear valid
  obtain ⟨countsEq, sizeEq, total⟩ := verifyOperandSegmentSizes_spec getCounts
  split at rest <;> try contradiction
  split at rest <;> try contradiction
  rename_i hDefaultArg
  have trueTypes := bind_ok_left rest
  replace rest := Except.ok_of_bind_ok rest
  obtain ⟨out, loop, rest⟩ := Except.bind_eq_ok.mp rest
  split at rest <;> try contradiction
  rename_i hEnd
  clear rest getCounts
  have srcCount : 1 + counts[1]! + counts[2]! = branch.getNumOperands! ctx.raw := by
    calc _ = counts.foldl (· + ·) 0 := (conditionalOperandCount (.inl rfl) sizeEq (by
          intro i hi
          have : i = 0 := by omega
          subst i
          exact Classical.not_not.mp ‹¬counts[0]! ≠ 1›)).symm
         _ = _ := total
  have dcEq : defaultCount.toNat = counts[1]! := by
    obtain ⟨bound, eq⟩ := Array.getElem?_eq_some_iff.mp hDefault
    rw [countsEq, getElem!_pos _ (1 : Nat) (by simpa [props] using bound), Array.getElem_map]
    exact congrArg Int.toNat eq.symm
  have base0 : successorSegmentStart 1 sizes 0 = 1 := by
    have empty : sizes.extract 1 1 = #[] := Array.ext (by simp; omega) (by simp)
    simp [successorSegmentStart, empty]
  have end0 := segmentStart_succ (fixed := 1) (i := 0) (sizes := sizes)
    (count := defaultCount) (by simp [sizes, Array.getElem?_append])
  let base (i : Nat) := successorSegmentStart 1 sizes (i + 1)
  have baseZero : base 0 = 1 + counts[1]! := by simpa [base0, dcEq, base] using end0
  let cases := props.case_operand_segments.values
  let P (i : Nat) := cases[i]!.toNat = (branch.getSuccessor! ctx.raw (i + 1)).getNumArguments! ctx.raw ∧
    ∃ msg, branch.verifyBranchSuccessorArgTypes ctx (base i) (branch.getSuccessor! ctx.raw (i + 1)) msg = .ok ()
  rw [← baseZero] at loop
  have caseInfo := rangeCountLoop cases.size base P (h := loop) (by
    intro i hi s h
    split at h <;> try contradiction
    split at h <;> try contradiction
    have inc := Except.ok_of_bind_ok h
    have stepBase := segmentStart_succ (fixed := 1) (i := i + 1) (sizes := sizes)
      (count := cases[i]!) (by
        simp [sizes, cases, Array.getElem?_append, hi, Nat.add_comm 1])
    refine ⟨?_, Classical.not_not.mp ‹¬ _›, _, bind_ok_left h⟩
    apply Eq.trans (Except.ok.inj inc.symm)
    congr 1
    exact stepBase.symm)
  obtain ⟨c, hc, start, array⟩ := segmentedSuccessorOperands_spec run
  have edgeMax : edge ≤ cases.size := by
    have h := (Array.getElem?_eq_some_iff.mp hc).1
    simp [sizes] at h
    exact (show edge ≤ props.case_operand_segments.values.size by omega)
  have hBaseCount : ∃ msg,
      c.toNat = (branch.getSuccessor! ctx.raw edge).getNumArguments! ctx.raw ∧
      branch.verifyBranchSuccessorArgTypes ctx s.beginOperandIndex (branch.getSuccessor! ctx.raw edge) msg = .ok () := by
    cases edge with
    | zero =>
      have cEq : c = defaultCount := by simpa [sizes, Array.getElem?_append] using hc.symm
      exact ⟨_, cEq ▸ dcEq.trans (Classical.not_not.mp hDefaultArg), start.trans base0 ▸ trueTypes⟩
    | succ i =>
      have ib : i < cases.size := by omega
      obtain ⟨ct, msg, vt⟩ := caseInfo.2 i ib
      have cEq : c = cases[i]! := by
        simpa [sizes, Array.getElem?_append, show ¬1+(i+1)<2 by omega, cases, Nat.add_comm 1,
          getElem!_pos cases i ib, ib] using hc.symm
      exact ⟨msg, cEq ▸ ct, start ▸ vt⟩
  obtain ⟨msg, arity, check⟩ := hBaseCount
  have inc := segmentStart_succ hc
  have le := segmentStart_mono (fixed := 1) (sizes := sizes) (i := edge+1)
    (j := cases.size+1) (by omega)
  have fin : out = branch.getNumOperands! ctx.raw := (Classical.not_not.mp hEnd).trans srcCount
  have lim : s.beginOperandIndex + (branch.getSuccessor! ctx.raw edge).getNumArguments! ctx.raw ≤
      branch.getNumOperands! ctx.raw := by
    dsimp only [base] at caseInfo
    omega
  refine ⟨?_, lim, fun hi ht => verifyBranchSuccessorArgTypes_integer check hi ht⟩
  rw [array, Array.size_extract, arity]
  have sizeOps := OperationPtr.getOperands!.size_eq_getNumOperands! (op := branch) (ctx := ctx.raw)
  omega

end Veir.Legalization.CTreeProofs
