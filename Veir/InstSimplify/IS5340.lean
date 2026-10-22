import Veir.InstSimplify.GEPPoisonSchema
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify
/-- Poison base pointer with arbitrary static GEP index metadata; no dynamic operand slots. -/
def IS5340_static : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := LLVM.PointerType)
    let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .getelementptr) #[poison.res[0]!] #[ty]
      (fun p => p.rawConstantIndices.values.all (· != -2147483648))
    return ty)
  (fun ty => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun p => p)

theorem IS5340_static_valid : Pattern.Valid IS5340_static := by
  simp only [IS5340_static]
  provePuddleValid
  rintro ⟨⟩ pp pv pi gp gv hg gi
  obtain rfl := (ptr_poison_iff _ _).mp pi
  obtain rfl := gep_poison_base_static gp gv gi
  refine ⟨_, (ptr_poison_iff _ _).mpr rfl, ?_⟩
  simp [RuntimeValue.isRefinedBy, isRefinedBy]
/-- The two source causes: a poison base, or a poison integer index in any dynamic slot. -/
inductive GEPPoisonCause where
  | base (dynamicCount : Nat)
  | index (before after : Nat)

def IS5340 (cause : GEPPoisonCause) : Pattern OpCode :=
  match cause with
  | .base n => gepPoisonBaseFamily n
  | .index before after => gepPoisonIndexFamily before after

theorem IS5340_valid (cause : GEPPoisonCause) : Pattern.Valid (IS5340 cause) := by
  cases cause with
  | base n => exact gepPoisonBaseFamily_valid n
  | index before after => exact gepPoisonIndexFamily_valid before after

end Veir.InstSimplify
