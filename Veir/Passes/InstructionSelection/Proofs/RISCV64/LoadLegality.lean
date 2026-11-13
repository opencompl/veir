module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common

namespace Veir

attribute [local implicit_reducible] TypeAttr

private theorem query_load (q : LegalityQuery (GMIR.propertiesOf .g_load))
    (h : riscv64LegalizerInfo.getActionFor .g_load q = .legal) :
    ((q.getLLT! (.type 0) = .scalar 64 ∨ q.getLLT! (.type 0) = .pointer 0) ∧
      q.getLLT! (.type 1) = .pointer 0) ∧
      (q.getLLT! (.type 0) = .pointer 0 → q.properties.size.toNat = 64) := by
  change (([LegalizeRule.legalForTypesWithMemDesc
    [⟨.scalar 64, .pointer 0, 8, 8⟩, ⟨.scalar 64, .pointer 0, 16, 16⟩,
      ⟨.scalar 64, .pointer 0, 32, 32⟩, ⟨.scalar 64, .pointer 0, 64, 64⟩,
      ⟨.pointer 0, .pointer 0, 64, 64⟩],
    LegalizeRule.widenScalarToNextPow2 (.type 0), LegalizeRule.minScalar (.type 0) 64]).findSome?
      (· q)).getD .unsupported = .legal at h
  simp only [List.findSome?_cons, LegalizeRule.legalForTypesWithMemDesc, LegalizeRule.legalIf,
    List.any_cons, List.any_nil, Bool.or_false] at h
  split at h
  · rename_i ht
    split at ht
    · rename_i hc
      simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
      rcases hc with h | h | h | h | h
      all_goals
        refine ⟨⟨by first | exact .inl h.1.1.1 | exact .inr h.1.1.1, h.1.1.2⟩, ?_⟩
        intro hp
        first
        | exact h.1.2
        | have impossible := hp.symm.trans h.1.1.1
          cases impossible
    · contradiction
  · simp only [LegalizeRule.widenScalarToNextPow2, LegalizeRule.minScalar,
      LegalizeRule.widenScalarIf] at h
    cases ht : q.getLLT! (.type 0) with
    | scalar width =>
      by_cases hp : width.nextPowerOfTwo = width <;>
        simp only [ht, hp, ↓reduceIte] at h <;>
        repeat' split at h <;> simp_all
      all_goals cases h
    | pointer space =>
      simp only [ht] at h
      repeat' split at h <;> simp_all

/-- Legal RISC-V generic loads use a 64-bit result and a pointer address. -/
theorem isLegal_g_load_types (dst src : TypeAttr) (props : GMIR.propertiesOf .g_load)
    (h : riscv64LegalizerInfo.isLegal .g_load #[dst, src] props = true) :
    ((∃ sign, dst = TypeAttr.of IntegerType ⟨64, sign⟩) ∨
      (∃ p : LLVM.PointerType, p.addressSpace = 0 ∧ dst = TypeAttr.of LLVM.PointerType p)) ∧
      (∃ p : LLVM.PointerType, p.addressSpace = 0 ∧ src = TypeAttr.of LLVM.PointerType p) := by
  have hllt : (LLT.ofType? dst = some (.scalar 64) ∨ LLT.ofType? dst = some (.pointer 0)) ∧
      LLT.ofType? src = some (.pointer 0) := by
    unfold LegalizerInfo.isLegal at h
    cases hq : LegalityQuery.ofTypes? #[dst, src] props with
    | none => simp [hq] at h
    | some q =>
      simp only [hq] at h
      have hlegal : riscv64LegalizerInfo.getActionFor .g_load q = .legal := by
        split at h <;> simp_all
      have htypes := (query_load q hlegal).1
      cases hd : LLT.ofType? dst <;> cases hs : LLT.ofType? src <;>
        simp [LegalityQuery.ofTypes?, Array.mapM, ↓Array.mapM.map, hd, hs] at hq
      cases hq
      simpa [LegalityQuery.getLLT!] using htypes
  rcases hllt with ⟨hd, hs⟩
  constructor
  · rcases hd with hd | hd
    · left
      rcases dst with ⟨attr, ht⟩
      cases attr <;> simp only [LLT.ofType?, Option.some.injEq, reduceCtorEq, LLT.scalar.injEq] at hd
      rename_i integer
      rcases integer with ⟨w, sign⟩
      cases hd
      exact ⟨sign, rfl⟩
    · right
      rcases dst with ⟨attr, ht⟩
      cases attr <;> simp only [LLT.ofType?, Option.some.injEq, reduceCtorEq, LLT.pointer.injEq] at hd
      rename_i p
      exact ⟨p, hd, rfl⟩
  · rcases src with ⟨attr, ht⟩
    cases attr <;> simp only [LLT.ofType?, Option.some.injEq, reduceCtorEq, LLT.pointer.injEq] at hs
    rename_i p
    exact ⟨p, hs, rfl⟩

/-- A pointer-valued legal load reads all sixty-four pointer bits. -/
theorem isLegal_g_load_pointer_size (dst : LLVM.PointerType) (src : TypeAttr)
    (props : GMIR.propertiesOf .g_load)
    (h : riscv64LegalizerInfo.isLegal .g_load #[TypeAttr.of LLVM.PointerType dst, src] props = true) :
    props.size.toNat = 64 := by
  unfold LegalizerInfo.isLegal at h
  cases hq : LegalityQuery.ofTypes? #[TypeAttr.of LLVM.PointerType dst, src] props with
  | none => simp [hq] at h
  | some q =>
    simp only [hq] at h
    have hlegal : riscv64LegalizerInfo.getActionFor .g_load q = .legal := by
      split at h <;> simp_all
    have htypes := query_load q hlegal
    have hd : LLT.ofType? (TypeAttr.of LLVM.PointerType dst) = some (.pointer dst.addressSpace) := by
      simp [LLT.ofType?, TypeAttr.of_def, ←Attribute.llvmPointerType_eq_of]
    cases hs : LLT.ofType? src <;>
      simp [LegalityQuery.ofTypes?, Array.mapM, ↓Array.mapM.map, hd, hs] at hq
    cases hq
    simp only [LegalityQuery.getLLT!] at htypes
    rcases htypes.1.1 with impossible | hp
    · cases impossible
    · exact htypes.2 hp

end Veir
