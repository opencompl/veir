module

public import Veir.Interpreter.Lemmas
public import Veir.Verifier
import all Veir.Verifier.Basic
import all Veir.Verifier.Lemmas
import all Veir.Verifier
import all Veir.Dialects.GMIR.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Interpreter.Memory
import all Veir.IR.Basic
import all Veir.IR.OpCode
import all Veir.IR.Attribute
import Veir.ForLean

public section

/-!
# The results of gMIR operations conform to their types

A verified gMIR operation with operands that conform to their types returns, if its interpretation
succeeds, results that conform to its result types (`OpCode.resultsConform`). An operation either
computes its results from an operand whose type group the verifier makes match the type group of
the result, or builds its results from its result types.
-/

namespace Veir

variable {ctx : WfIRContext OpCode} {op : OperationPtr} {opIn : op.InBounds ctx.raw}

/-! ## Conformance -/

/-- The width alone decides whether an integer conforms. -/
private theorem int_conforms {w : Nat} {x y : Data.LLVM.Int w} {ty : TypeAttr}
    (h : (RuntimeValue.int w x).Conforms ty) : (RuntimeValue.int w y).Conforms ty := by
  obtain ⟨a, _⟩ := ty; cases a <;> exact h

private theorem int_conforms_of_val {w : Nat} {x : Data.LLVM.Int w} {ty : TypeAttr}
    {it : IntegerType} (h : ty.val = .integerType it) (hw : it.bitwidth = w) :
    (RuntimeValue.int w x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; exact hw

/-- An integer conforms to an integer type of its width. -/
private theorem bitwidth_of_conforms {w : Nat} {x : Data.LLVM.Int w} {ty : TypeAttr}
    {it : IntegerType} (h : ty.val = .integerType it) (hc : (RuntimeValue.int w x).Conforms ty) :
    it.bitwidth = w := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; exact hc

private theorem byte_conforms_of_val {w : Nat} {x : Data.LLVM.Byte w} {ty : TypeAttr}
    {bt : LLVM.ByteType} (h : ty.val = .byteType bt) (hw : bt.bitwidth = w) :
    (RuntimeValue.byte w x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; simp only at h; subst h; exact hw

private theorem addr_conforms_of_val {x : Data.LLVM.Ptr} {ty : TypeAttr}
    (h : ∃ p, ty.val = .llvmPointerType p) : (RuntimeValue.addr x).Conforms ty := by
  obtain ⟨a, _⟩ := ty; obtain ⟨p, h⟩ := h; simp only at h; subst h; trivial

private theorem bitwidthOfType_integerType {it : IntegerType} :
    Attribute.bitwidthOfType (Attribute.of IntegerType it) = some it.bitwidth := rfl

private theorem array_size_eq_two {α : Type} {xs : Array α} (h : xs.size = 2) :
    ∃ a b, xs = #[a, b] := by
  rcases xs with ⟨_ | ⟨a, _ | ⟨b, _ | _⟩⟩⟩
  · simp at h
  · simp at h
  · exact ⟨a, b, rfl⟩
  · simp at h

private theorem operand_conforms {operands : Array RuntimeValue} {O : Array TypeAttr}
    (h : RuntimeValue.ArrayConforms operands O) {i : Nat} {v : RuntimeValue}
    (hv : operands[i]? = some v) : v.Conforms O[i]! := by
  rw [Array.getElem?_eq_some_iff] at hv
  obtain ⟨hi, rfl⟩ := hv
  simpa [getElem!_pos operands i hi] using h.2 i hi

private theorem results_zero {R : Array TypeAttr} (hR : R.size = 0) :
    RuntimeValue.ArrayConforms #[] R :=
  ⟨by simp [hR], by simp⟩

private theorem results_one {v : RuntimeValue} {R : Array TypeAttr} (hR : R.size = 1)
    (hv : v.Conforms R[0]!) : RuntimeValue.ArrayConforms #[v] R := by
  refine ⟨by simp [hR], fun i hi => ?_⟩
  obtain rfl : i = 0 := by simp at hi; omega
  simpa using hv

private theorem results_two {v v' : RuntimeValue} {R : Array TypeAttr} (hR : R.size = 2)
    (hv : v.Conforms R[0]!) (hv' : v'.Conforms R[1]!) : RuntimeValue.ArrayConforms #[v, v'] R := by
  refine ⟨by simp [hR], fun i hi => ?_⟩
  simp only [List.size_toArray, List.length_cons, List.length_nil] at hi
  obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
  · simpa using hv
  · simpa using hv'

/-- A single result conforms to result types that are a single type it conforms to. -/
private theorem results_getElem? {v : RuntimeValue} {R : Array TypeAttr} {t : TypeAttr}
    (hR : R.size = 1) (ht : R[0]? = some t) (hv : v.Conforms t) :
    RuntimeValue.ArrayConforms #[v] R := by
  refine results_one hR ?_
  rwa [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, ht, Option.getD_some]

/-- A single result conforms to result types that are a single type it conforms to. -/
private theorem results_toList {v : RuntimeValue} {R : Array TypeAttr} {t : TypeAttr}
    (ht : R.toList = [t]) (hv : v.Conforms t) : RuntimeValue.ArrayConforms #[v] R := by
  obtain rfl : R = #[t] := List.eq_toArray_iff.mpr ht
  exact results_one rfl (by simpa using hv)

/-! ## Interpretation -/

private theorem Interp.exists_of_bind_eq_ok {α β : Type} {x : Interp α} {f : α → Interp β}
    {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp_all

/-- A load returns a value of the type it loads. -/
private theorem llvmLoad_conforms {mem : MemoryState} {p : Data.Pointer} {t : TypeAttr}
    {v : RuntimeValue} (h : mem.llvmLoad p t = .ok v) : v.Conforms t := by
  simp only [MemoryState.llvmLoad] at h
  split at h
  · simp at h
  split at h <;>
    (repeat' (first
      | (obtain ⟨_, -, h⟩ := Interp.exists_of_bind_eq_ok h)
      | split at h)) <;>
    (try simp only [Interp.pure_eq, Interp.ok.injEq] at h) <;> (try subst h) <;>
    first
      | (simp at h; done)
      | exact int_conforms_of_val ‹_› rfl
      | exact byte_conforms_of_val ‹_› rfl
      | exact addr_conforms_of_val ⟨_, ‹_›⟩

private theorem vals_of_ok {vs vals : Array RuntimeValue} {m m' : MemoryState}
    {a a' : Option ControlFlowAction}
    (h : (Interp.ok (vs, m, a) : Interp _) = .ok (vals, m', a')) : vals = vs := by
  simp only [Interp.ok.injEq, Prod.mk.injEq] at h; exact h.1.symm

/-! ## Verifier -/

/-- The first check of a successful sequence of checks succeeds. -/
private theorem bind_ok_left {ε α : Type} {x : Except ε PUnit} {f : PUnit → Except ε α}
    {a : α} (h : (x >>= f) = .ok a) : x = .ok () := by
  cases x with
  | ok u => rfl
  | error e => simp [bind, Except.bind] at h

private theorem gmirVerified {opT : GMIR} (hType : op.getOpType! ctx.raw = .gmir opT)
    (hV : op.Verified ctx opIn) : GMIR.verifyLocalInvariants opT op ctx opIn = .ok () := by
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, OpCode.verifyLocalInvariants,
    ← OperationPtr.getOpType!_eq_getOpType, hType] at hV
  exact hV

/--
What every step of a successful loop that only yields or throws establishes holds for every element.
-/
private theorem Except.forIn_list_ok {α ε : Type} {l : List α}
    {f : α → PUnit → Except ε (ForInStep PUnit)} (P : α → Prop)
    (hf : ∀ a s, f a PUnit.unit = .ok s → s = .yield PUnit.unit ∧ P a)
    (h : forIn l PUnit.unit f = .ok PUnit.unit) : ∀ a ∈ l, P a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.forIn_cons] at h
    rcases hfa : f a PUnit.unit with e | s <;> rw [hfa] at h
    · simp [bind, Except.bind] at h
    · obtain ⟨rfl, hP⟩ := hf a _ hfa
      simp only [bind, Except.bind] at h
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hP
      · exact ih h b hb

private theorem Except.forIn_range_ok {ε : Type} {n : Nat}
    {f : Nat → PUnit → Except ε (ForInStep PUnit)} (P : Nat → Prop)
    (hf : ∀ a s, f a PUnit.unit = .ok s → s = .yield PUnit.unit ∧ P a)
    (h : forIn [0:n] PUnit.unit f = .ok PUnit.unit) : ∀ i < n, P i := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  intro i hi
  exact Except.forIn_list_ok P hf h i (by simp [List.mem_range'_1]; omega)

private theorem Except.forIn_array_ok {α ε : Type} {arr : Array α}
    {f : α → PUnit → Except ε (ForInStep PUnit)} (P : α → Prop)
    (hf : ∀ a s, f a PUnit.unit = .ok s → s = .yield PUnit.unit ∧ P a)
    (h : forIn arr PUnit.unit f = .ok PUnit.unit) : ∀ a ∈ arr, P a := by
  rw [← Array.forIn_toList] at h
  intro a ha
  exact Except.forIn_list_ok P hf h a (Array.mem_toList_iff.mpr ha)

private theorem verifyNonOperandCounts_ok {r g s : Nat}
    (h : op.verifyNonOperandCounts ctx opIn r g s = .ok ()) : op.getNumResults! ctx.raw = r := by
  rw [OperationPtr.getNumResults!_eq_getNumResults opIn]
  simp only [OperationPtr.verifyNonOperandCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · rename_i hne; simpa using hne

private theorem verifyPlainOpCounts_ok {o r : Nat}
    (h : op.verifyPlainOpCounts ctx opIn o r = .ok ()) : op.getNumResults! ctx.raw = r := by
  simp only [OperationPtr.verifyPlainOpCounts, OperationPtr.verifyOpCounts] at h
  split at h
  · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  · exact verifyNonOperandCounts_ok h

private theorem verifyTerminatorCounts_ok {s : Nat}
    (h : op.verifyTerminatorCounts ctx opIn s = .ok ()) : op.getNumResults! ctx.raw = 0 :=
  verifyNonOperandCounts_ok h

/-- The members of a type group have the same type. -/
private theorem typedGroups_ok {arr : Array (TypeGroup × TypeAttr)}
    {canon : Std.HashMap TypeGroup TypeAttr} {e : TypeGroup × TypeAttr → String}
    (h : forIn arr PUnit.unit (fun x (_ : PUnit) =>
      if (canon[x.1]! != x.2) = true then
        (do throw (e x); pure (ForInStep.yield PUnit.unit) : Except String _)
      else pure (ForInStep.yield PUnit.unit)) = .ok PUnit.unit)
    {g : TypeGroup} {t t' : TypeAttr} (ht : (g, t) ∈ arr) (ht' : (g, t') ∈ arr) : t = t' := by
  have hP := Except.forIn_array_ok (fun x => canon[x.1]! = x.2) (fun a s hs => by
    split at hs
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs
    · rename_i hne
      simp only [pure, Except.pure, Except.ok.injEq] at hs
      exact ⟨hs.symm, by simpa using hne⟩) h
  exact (hP _ ht).symm.trans (hP _ ht')

private theorem mem_typedGroups_result {opT : GMIR} {i : Nat} {g : TypeGroup}
    (hg : opT.genericOpInfo.outOperandList[i]? = some g)
    (hi : i < (op.getResultTypes! ctx.raw).size) :
    (g, (op.getResultTypes! ctx.raw)[i]!) ∈ opT.getTypedGroups! op ctx.raw := by
  rw [Array.getElem?_eq_some_iff] at hg
  obtain ⟨hi', hg⟩ := hg
  simp only [GMIR.getTypedGroups!, Array.mem_append]
  left
  rw [Array.mem_iff_getElem]
  refine ⟨i, by simp; omega, ?_⟩
  rw [Array.getElem_zip, hg, getElem!_pos _ i hi]

private theorem mem_typedGroups_operand {opT : GMIR} {i : Nat} {g : TypeGroup}
    (hg : opT.genericOpInfo.inOperandList[i]? = some g)
    (hi : i < (op.getOperandTypes! ctx.raw).size) :
    (g, (op.getOperandTypes! ctx.raw)[i]!) ∈ opT.getTypedGroups! op ctx.raw := by
  rw [Array.getElem?_eq_some_iff] at hg
  obtain ⟨hi', hg⟩ := hg
  simp only [GMIR.getTypedGroups!, Array.mem_append]
  right
  rw [Array.mem_iff_getElem]
  refine ⟨i, by simp; omega, ?_⟩
  rw [Array.getElem_zip, hg, getElem!_pos _ i hi]

/--
The checks of the verifier that all non-branch gMIR operations share: the number of results, and
that the members of a type group have the same type.
-/
private theorem gmir_verify_common {opT : GMIR} (hb : opT ≠ .g_br ∧ opT ≠ .g_brcond)
    (h : GMIR.verifyLocalInvariants opT op ctx opIn = .ok ()) :
    op.getNumResults! ctx.raw = opT.genericOpInfo.outOperandList.size ∧
    ∀ g t t', (g, t) ∈ opT.getTypedGroups! op ctx.raw →
      (g, t') ∈ opT.getTypedGroups! op ctx.raw → t = t' := by
  unfold GMIR.verifyLocalInvariants at h
  simp only at h
  rw [ite_eq_left (by cases opT <;> simp_all)] at h
  refine ⟨verifyPlainOpCounts_ok (bind_ok_left h), fun g t t' ht ht' => ?_⟩
  exact typedGroups_ok (bind_ok_left (Except.ok_of_bind_ok h)) ht ht'

private theorem ite_throw_ok {ε : Type} {c : Prop} [Decidable c] {e : ε}
    (h : (if c then throw e else pure () : Except ε PUnit) = .ok ()) : ¬c := by
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · assumption

/-- The opcode-specific checks of the verifier for a gMIR operation that is not a branch. -/
private theorem gmir_verify_specific {opT : GMIR} (hb : opT ≠ .g_br ∧ opT ≠ .g_brcond)
    (h : GMIR.verifyLocalInvariants opT op ctx opIn = .ok ()) :
    (match opT with
      | .g_icmp => do
        op.checkIsNonNullIntegerType ctx opIn
        op.verifyGMIRICmp ctx opIn
      | .g_merge_values | .g_unmerge_values => do
        op.checkIsNonNullIntegerType ctx opIn
        op.verifyGMIRIntegerTypes ctx opIn
        op.verifyGMIRTotalWidth ctx opIn
      | .g_inttoptr => do
        op.checkIsNonNullIntegerType ctx opIn
        ((op.getOperand! ctx.raw 0).getType! ctx.raw).verifyIntegerType
          "gmir.g_inttoptr: Expected operand 0 to have integer type"
        ((op.getResult 0).getType! ctx.raw).verifyLlvmPointerType
          "gmir.g_inttoptr: Expected result to have !llvm.ptr type"
      | .g_uaddo | .g_uadde | .g_usubo | .g_usube | .g_saddo | .g_ssubo => do
        op.checkIsNonNullIntegerType ctx opIn
        op.verifyGMIRIntegerTypes ctx opIn
        let carryType := (op.getResult 1).getType! ctx.raw
        if carryType.val ≠ .integerType (.signless 1) then
          let instrName := String.fromUTF8! (IsOpCode.name (op.getOpType ctx.raw opIn))
          throw s!"{instrName}: Expected the carry to have type i1, but got {carryType}"
      | _ => pure () : Except String PUnit) = .ok () := by
  unfold GMIR.verifyLocalInvariants at h
  simp only at h
  rw [ite_eq_left (by cases opT <;> simp_all)] at h
  have h' := Except.ok_of_bind_ok (Except.ok_of_bind_ok h)
  cases opT <;> first | rfl | exact h' | simp_all

/-- The type of a result, as an element of the result types. -/
private theorem resultType_eq {i : Nat} (hi : i < op.getNumResults ctx.raw opIn) :
    (op.getResult i).getType! ctx.raw = (op.getResultTypes! ctx.raw)[i]! := by
  rw [OperationPtr.getResultTypes!.getElem!_eq]
  rwa [OperationPtr.getNumResults!_eq_getNumResults opIn]

/-- The type of an operand, as an element of the operand types. -/
private theorem operandType_eq {i : Nat} (hi : i < op.getNumOperands ctx.raw opIn) :
    (op.getOperand! ctx.raw i).getType! ctx.raw = (op.getOperandTypes! ctx.raw)[i]! := by
  rw [OperationPtr.getOperandTypes!.getElem!_eq]
  rwa [OperationPtr.getNumOperands!_eq_getNumOperands opIn]

/-- A result of integer type is not `i0`. -/
private theorem checkIsNonNullIntegerType_result
    (h : op.checkIsNonNullIntegerType ctx opIn = .ok ())
    {i : Nat} (hi : i < op.getNumResults ctx.raw opIn) {it : IntegerType}
    (hit : ((op.getResult i).getType! ctx.raw).val = .integerType it) : it.bitwidth ≠ 0 := by
  simp only [OperationPtr.checkIsNonNullIntegerType] at h
  have h2 := bind_ok_left (Except.ok_of_bind_ok h)
  refine Except.forIn_range_ok
    (fun i => ∀ it, ((op.getResult i).getType! ctx.raw).val = .integerType it →
      it.bitwidth ≠ 0)
    (fun a s hs => ?_) h2 i hi it hit
  split at hs
  · next it' hT =>
    split at hs
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs
    · rename_i hne
      refine ⟨?_, fun it hit => ?_⟩
      · split at hs <;>
          simp_all [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure]
      · rw [hT] at hit; cases hit; exact hne
  · next hT =>
    exact ⟨by simp_all [pure, Except.pure], fun it hit => absurd hit (hT it)⟩

/-- The operands and the results of an operation that `verifyGMIRIntegerTypes` accepts are integers.
-/
private theorem verifyGMIRIntegerTypes_ok (h : op.verifyGMIRIntegerTypes ctx opIn = .ok ()) :
    (∀ i < op.getNumOperands ctx.raw opIn,
      ∃ it, ((op.getOperand! ctx.raw i).getType! ctx.raw).val = .integerType it) ∧
    (∀ i < op.getNumResults ctx.raw opIn,
      ∃ it, ((op.getResult i).getType! ctx.raw).val = .integerType it) := by
  simp only [OperationPtr.verifyGMIRIntegerTypes] at h
  constructor
  · refine Except.forIn_range_ok _ (fun a s hs => ?_) (bind_ok_left h)
    simp only [TypeAttr.verifyIntegerType] at hs
    split at hs
    · next _ hT =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hs
      exact ⟨hs.symm, _, hT⟩
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs
  · refine Except.forIn_range_ok _ (fun a s hs => ?_) (bind_ok_left (Except.ok_of_bind_ok h))
    simp only [TypeAttr.verifyIntegerType] at hs
    split at hs
    · next _ hT =>
      simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hs
      exact ⟨hs.symm, _, hT⟩
    · simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hs

private theorem verifyLlvmPointerType_ok {ty : TypeAttr} {msg : String}
    (h : ty.verifyLlvmPointerType msg = .ok ()) : ∃ p, ty.val = .llvmPointerType p := by
  simp only [TypeAttr.verifyLlvmPointerType] at h
  split at h
  · exact ⟨_, by assumption⟩
  · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- A gMIR branch has no results. -/
private theorem gmir_verify_branch {opT : GMIR} (hb : opT = .g_br ∨ opT = .g_brcond)
    (h : GMIR.verifyLocalInvariants opT op ctx opIn = .ok ()) : op.getNumResults! ctx.raw = 0 := by
  rcases hb with rfl | rfl <;> unfold GMIR.verifyLocalInvariants at h <;>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
  · have h' := Except.ok_of_bind_ok (Except.ok_of_bind_ok h)
    simp only [OperationPtr.verifyUnconditionalBranch] at h'
    exact verifyTerminatorCounts_ok (bind_ok_left h')
  · exact verifyTerminatorCounts_ok (bind_ok_left (Except.ok_of_bind_ok (Except.ok_of_bind_ok h)))

/-- The total width of `verifyGMIRTotalWidth`. -/
private theorem verifyGMIRTotalWidth_ok (h : op.verifyGMIRTotalWidth ctx opIn = .ok ()) :
    (op.getResultTypes! ctx.raw).foldl
        (fun width type => width + (Attribute.bitwidthOfType type.val).getD 0) 0 =
      (op.getOperandTypes! ctx.raw).foldl
        (fun width type => width + (Attribute.bitwidthOfType type.val).getD 0) 0 := by
  simp only [OperationPtr.verifyGMIRTotalWidth] at h
  exact Classical.byContradiction (ite_throw_ok h)

/-!
## The opcodes

Each tactic below peels the interpretation of an opcode down to the results it returns.
-/

set_option hygiene false in
local macro "rc_peel" : tactic => `(tactic| (
  simp only [GMIR.interpretOp'] at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := Interp.exists_of_bind_eq_ok h)
    | split at h)
  all_goals try (simp at h; done)))

-- The number of results of a verified non-branch operation, and its type groups.
set_option hygiene false in
local macro "rc_common" n:num : tactic => `(tactic| (
  have hVL := gmirVerified hType hV
  obtain ⟨hN, hG⟩ := gmir_verify_common (by decide) hVL
  have hR : (op.getResultTypes! ctx.raw).size = $n := by
    rw [OperationPtr.getResultTypes!.size_eq_getNumResults!, hN]; rfl
  have hN' : op.getNumResults ctx.raw opIn = $n := by
    rw [← OperationPtr.getNumResults!_eq_getNumResults opIn, hN]; rfl))

-- The results are built from the result types.
set_option hygiene false in
local macro "rc_restype" : tactic => `(tactic| (
  rc_common 1
  rc_peel
  all_goals (obtain rfl := vals_of_ok h
             first
               | exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› rfl)
               | exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› ‹_›))))

-- The first result has the type of operand `k`, and all results are integers of its width.
set_option hygiene false in
local macro "rc_same" n:num k:num : tactic => `(tactic| (
  rc_common $n
  simp only [GMIR.interpretOp'] at h
  split at h
  · rename_i hOps
    obtain rfl := List.eq_toArray_iff.mpr hOps
    have hEq := hG _ _ _ (mem_typedGroups_result (i := 0) rfl (by omega))
      (mem_typedGroups_operand (i := $k) rfl (by rw [← hConf.1]; simp))
    have h0 := operand_conforms hConf (i := $k) rfl
    rw [← hEq] at h0
    repeat' split at h
    all_goals first
      | (simp at h; done)
      | (obtain rfl := vals_of_ok h
         first
           | exact results_one hR (int_conforms h0)
           | exact results_two hR (int_conforms h0) (int_conforms_of_val hC rfl))
  · simp at h))

-- The second result of an operation with a carry out is an `i1`.
set_option hygiene false in
local macro "rc_carry" : tactic => `(tactic| (
  have hS := gmir_verify_specific (by decide) (gmirVerified hType hV)
  simp only at hS
  have hC := Classical.not_not.mp (ite_throw_ok (Except.ok_of_bind_ok (Except.ok_of_bind_ok hS)))
  rw [resultType_eq (by rw [← OperationPtr.getNumResults!_eq_getNumResults opIn,
    (gmir_verify_common (by decide) (gmirVerified hType hV)).1]; decide)] at hC
  rc_same 2 0))

/--
A verified gMIR operation with operands that conform to their types returns, if its
interpretation succeeds, results that conform to its result types.
-/
theorem GMIR.interpretOp'_results_conform (opT : GMIR)
    (hType : op.getOpType! ctx.raw = .gmir opT) (hV : op.Verified ctx opIn)
    (hConf : RuntimeValue.ArrayConforms operands (op.getOperandTypes! ctx.raw))
    (h : GMIR.interpretOp' opT (op.getProperties! ctx.raw (OpCode.gmir opT))
      (op.getResultTypes! ctx.raw) operands bs mem = .ok (vals, mem', act)) :
    RuntimeValue.ArrayConforms vals (op.getResultTypes! ctx.raw) := by
  cases opT
  case g_add | g_sub | g_mul | g_and | g_or | g_xor | g_sdiv | g_udiv | g_srem | g_urem
     | g_saddsat | g_uaddsat | g_ssubsat | g_usubsat | g_smin | g_smax | g_umin | g_umax
     | g_shl | g_lshr | g_ashr | g_sshlsat | g_ushlsat | g_rotl | g_rotr | g_fshl | g_fshr
     | g_bswap | g_bitreverse | g_brev8 | g_abs | g_sext_inreg =>
    rc_same 1 0
  case g_select => rc_same 1 1
  case g_uaddo | g_uadde | g_usubo | g_usube | g_saddo | g_ssubo => rc_carry
  case g_anyext | g_sext | g_zext | g_trunc | g_constant | g_ptrtoint
     | g_ctlz | g_cttz | g_ctlz_zero_poison | g_cttz_zero_poison | g_ctpop => rc_restype
  case g_icmp =>
    rc_common 1
    have hS := gmir_verify_specific (by decide) hVL
    simp only at hS
    have hNZ : ∀ it, ((op.getResultTypes! ctx.raw)[0]!).val = .integerType it →
        it.bitwidth ≠ 0 := fun it hit =>
      checkIsNonNullIntegerType_result (bind_ok_left hS) (i := 0) (by omega)
        (by rw [resultType_eq (by omega)]; exact hit)
    rc_peel
    all_goals (obtain rfl := vals_of_ok h)
    · exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› rfl)
    · rename_i resType hRes _ resBw hBw hlt
      have hR0 : (op.getResultTypes! ctx.raw)[0]! = resType := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, hRes, Option.getD_some]
      have := hNZ resBw (by rw [hR0, hBw])
      exact results_getElem? hR hRes (int_conforms_of_val hBw (by omega))
  case g_poison =>
    rc_common 1
    rc_peel
    all_goals (obtain rfl := vals_of_ok h
               first
                 | exact results_getElem? hR ‹_› (int_conforms_of_val ‹_› rfl)
                 | exact results_getElem? hR ‹_› (addr_conforms_of_val ⟨_, ‹_›⟩))
  case g_inttoptr =>
    rc_common 1
    have hS := gmir_verify_specific (by decide) hVL
    simp only at hS
    have hP := verifyLlvmPointerType_ok (Except.ok_of_bind_ok (Except.ok_of_bind_ok hS))
    rw [resultType_eq (by omega)] at hP
    rc_peel
    all_goals (obtain rfl := vals_of_ok h; exact results_one hR (addr_conforms_of_val hP))
  case g_load =>
    rc_peel
    all_goals (obtain rfl := vals_of_ok h
               first
                 | exact results_toList ‹_› (llvmLoad_conforms ‹_›)
                 | exact results_toList ‹_› (int_conforms_of_val ‹_› rfl))
  case g_store =>
    rc_common 0
    rc_peel
    all_goals (obtain rfl := vals_of_ok h; exact results_zero hR)
  case g_br | g_brcond =>
    have hR : (op.getResultTypes! ctx.raw).size = 0 := by
      rw [OperationPtr.getResultTypes!.size_eq_getNumResults!]
      exact gmir_verify_branch (by simp) (gmirVerified hType hV)
    rc_peel
    all_goals (obtain rfl := vals_of_ok h; exact results_zero hR)
  case g_merge_values =>
    rc_common 1
    have hS := gmir_verify_specific (by decide) hVL
    simp only at hS
    have hI := verifyGMIRIntegerTypes_ok (bind_ok_left (Except.ok_of_bind_ok hS))
    have hW := verifyGMIRTotalWidth_ok (Except.ok_of_bind_ok (Except.ok_of_bind_ok hS))
    simp only [GMIR.interpretOp'] at h
    split at h
    · rename_i w lo w' hi hOps
      obtain rfl := List.eq_toArray_iff.mpr hOps
      have hO : (op.getOperandTypes! ctx.raw).size = 2 := by rw [← hConf.1]; rfl
      have hNO : op.getNumOperands ctx.raw opIn = 2 := by
        rw [← OperationPtr.getNumOperands!_eq_getNumOperands opIn,
          ← OperationPtr.getOperandTypes!.size_eq_getNumOperands!, hO]
      obtain ⟨it, hit⟩ := hI.2 0 (by omega)
      obtain ⟨ia, hia⟩ := hI.1 0 (by omega)
      obtain ⟨ib, hib⟩ := hI.1 1 (by omega)
      rw [resultType_eq (by omega)] at hit
      rw [operandType_eq (by omega)] at hia hib
      have ha := bitwidth_of_conforms hia (operand_conforms hConf (i := 0) rfl)
      have hb := bitwidth_of_conforms hib (operand_conforms hConf (i := 1) rfl)
      obtain ⟨t, hRt⟩ := Array.size_eq_one_iff.mp hR
      obtain ⟨a, b, hOt⟩ := array_size_eq_two hO
      rw [hRt] at hW hit ⊢
      rw [hOt] at hW hia hib
      simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
        at hit hia hib
      simp [bitwidthOfType_integerType, hit, hia, hib] at hW
      repeat' split at h
      all_goals first
        | (simp at h; done)
        | (obtain rfl := vals_of_ok h
           exact results_one rfl (by simpa using int_conforms_of_val hit (by omega)))
    · simp at h
  case g_unmerge_values =>
    rc_common 2
    have hS := gmir_verify_specific (by decide) hVL
    simp only at hS
    have hI := verifyGMIRIntegerTypes_ok (bind_ok_left (Except.ok_of_bind_ok hS))
    have hW := verifyGMIRTotalWidth_ok (Except.ok_of_bind_ok (Except.ok_of_bind_ok hS))
    simp only [GMIR.interpretOp'] at h
    split at h
    · rename_i w x hOps
      obtain rfl := List.eq_toArray_iff.mpr hOps
      have hO : (op.getOperandTypes! ctx.raw).size = 1 := by rw [← hConf.1]; rfl
      have hNO : op.getNumOperands ctx.raw opIn = 1 := by
        rw [← OperationPtr.getNumOperands!_eq_getNumOperands opIn,
          ← OperationPtr.getOperandTypes!.size_eq_getNumOperands!, hO]
      have hEq := hG _ _ _ (mem_typedGroups_result (i := 0) rfl (by omega))
        (mem_typedGroups_result (i := 1) rfl (by omega))
      obtain ⟨it, hit⟩ := hI.2 0 (by omega)
      obtain ⟨ia, hia⟩ := hI.1 0 (by omega)
      rw [resultType_eq (by omega)] at hit
      rw [operandType_eq (by omega)] at hia
      have ha := bitwidth_of_conforms hia (operand_conforms hConf (i := 0) rfl)
      have hit1 : ((op.getResultTypes! ctx.raw)[1]!).val = .integerType it := hEq ▸ hit
      obtain ⟨t0, t1, hRt⟩ := array_size_eq_two hR
      obtain ⟨a, hOt⟩ := Array.size_eq_one_iff.mp hO
      rw [hRt] at hW hit hit1 ⊢
      rw [hOt] at hW hia
      simp only [List.getElem!_toArray, List.getElem!_cons_zero, List.getElem!_cons_succ]
        at hit hit1 hia
      simp [bitwidthOfType_integerType, hit, hit1, hia] at hW
      repeat' split at h
      all_goals first
        | (simp at h; done)
        | (obtain rfl := vals_of_ok h
           exact results_two rfl (by simpa using int_conforms_of_val hit (by omega))
             (by simpa using int_conforms_of_val hit1 (by omega)))
    · simp at h

/-- The results of every gMIR opcode conform to their types. -/
theorem OpCode.resultsConform_gmir (opT : GMIR) : OpCode.resultsConform (.gmir opT) := by
  refine OpCode.resultsConform_def.mpr
    fun ctx op opIn hType hV operands vals mem mem' act hConf h => ?_
  have hType! : op.getOpType! ctx.raw = .gmir opT := by
    rw [OperationPtr.getOpType!_eq_getOpType opIn]; exact hType
  simp only [OperationPtr.interpret] at h
  rw [hType!] at h
  exact GMIR.interpretOp'_results_conform opT hType! hV hConf h

/--
info: 'Veir.OpCode.resultsConform_gmir' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OpCode.resultsConform_gmir

instance (op : GMIR) : ResultsConform (.gmir op) :=
  ⟨OpCode.resultsConform_gmir op⟩

end Veir

end
