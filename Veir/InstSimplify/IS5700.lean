import Veir.InstSimplify.MiscSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def IS5700_int : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .bitcast) #[x] #[ty]
    return x)
  pure (fun x => x)
theorem IS5700_int_valid : Pattern.Valid IS5700_int := by
  simp only [IS5700_int]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro x rp rv ri
  have he := ri.2 MemoryState.empty
  try dsimp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp at he
  obtain rfl : rv = .int w x := by simpa using he.symm
  exact RuntimeValue.isRefinedBy_refl _

def IS5700_byte : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.ByteType) (fun _ => true)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .bitcast) #[x] #[ty]
    return x)
  pure (fun x => x)
theorem IS5700_byte_valid : Pattern.Valid IS5700_byte := by
  simp only [IS5700_byte]
  provePuddleValid
  rintro ⟨w⟩
  simp only [RuntimeValue.Conforms.byteType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro x rp rv ri
  have he := ri.2 MemoryState.empty
  try dsimp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp at he
  obtain rfl : rv = .byte w x := by simpa using he.symm
  exact RuntimeValue.isRefinedBy_refl _

def IS5700_ptr : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType) (fun _ => true)
    let x ← MatchProg.value ty
    let _ ← MatchProg.root (.llvm .bitcast) #[x] #[ty]
    return x)
  pure (fun x => x)
theorem IS5700_ptr_valid : Pattern.Valid IS5700_ptr := by
  simp only [IS5700_ptr]
  provePuddleValid
  rintro ⟨⟩
  simp only [RuntimeValue.Conforms.llvmPointerType, forall_exists_index, forall_eq_apply_imp_iff]
  rintro x rp rv ri
  have he := ri.2 MemoryState.empty
  try dsimp only [TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp only [interpretOp', Llvm.interpretOp', TypeAttr.of_def, Attribute.of_def, IsAttr.inject] at he
  simp at he
  obtain rfl : rv = .addr x := by simpa using he.symm
  exact RuntimeValue.isRefinedBy_refl _
end Veir.InstSimplify
