import Veir.InstSimplify.CastLogicSupport
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS2406
def pattern (commute : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let src ← MatchProg.type (Attr := IntegerType)
    let dst ← MatchProg.type (Attr := IntegerType)
    let x ← MatchProg.value src
    let z ← MatchProg.operation (.llvm .zext) #[x] #[dst]
    let s ← MatchProg.operation (.llvm .sext) #[x] #[dst]
    let _ ← MatchProg.root (.llvm .or) (cond commute #[s.res[0]!,z.res[0]!] #[z.res[0]!,s.res[0]!]) #[dst]
    return s.res[0]!) pure (fun x => x)

theorem semantic (w v : Nat) (x : LLVM.Int w) (nneg d : Bool) (hw : w < v) :
    RuntimeValue.int v (LLVM.Int.or (LLVM.Int.zext x v nneg hw) (LLVM.Int.sext x v hw) d) ⊒
      .int v (LLVM.Int.sext x v hw) := by
  cases x with
  | poison => simp [LLVM.Int.zext,LLVM.Int.sext,LLVM.Int.or,Id.run,pure,RuntimeValue.isRefinedBy,isRefinedBy]
  | val x =>
    rcases logic_zext_outcomes x v nneg hw with hz | hz
    all_goals simp only [hz,LLVM.Int.sext,LLVM.Int.or,Id.run,pure]
    all_goals (try split <;> simp_all [RuntimeValue.isRefinedBy,isRefinedBy,logic_zext_and_sext,logic_zext_or_sext])
    all_goals simp [RuntimeValue.isRefinedBy,isRefinedBy,logic_zext_and_sext,logic_zext_or_sext]

theorem valid (commute : Bool) : Pattern.Valid (pattern commute) := by
  cases commute
  all_goals
    simp only [pattern]
    provePuddleValid
    simp only [RuntimeValue.Conforms.integerType,forall_exists_index,forall_eq_apply_imp_iff]
    rintro ⟨w,ss⟩ ⟨v,ds⟩ x zp zv hz sp sv hs rp rv hr
    have hw := logic_zext_width_lt _ _ _ _ _ hz
    obtain rfl := (logic_zext_iff _ _ _ _ _ hw).mp hz
    obtain rfl := (sext_iff _ _ _ _ _ hw).mp hs
    obtain rfl := (or_iff _ _ _ _ _).mp hr
    simpa only [logic_and_comm,logic_or_comm] using semantic w v x zp.nneg rp.disjoint hw
end Veir.InstSimplify.IS2406
