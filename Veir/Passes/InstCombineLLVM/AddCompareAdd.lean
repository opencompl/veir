module
public import Veir.Passes.InstCombineLLVM.CompareSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo
namespace Veir.Passes.InstCombineLLVM.AddCompareAdd
open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by cases ‹Decidable p› <;> rfl
private inductive EqNe | eq | ne
private def EqNe.pred : EqNe → LLVM.IntPred | .eq => .eq | .ne => .ne
private def pattern (kind : EqNe) (leftCommuted rightCommuted : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let d ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .add) (match leftCommuted with
      | false => #[a, b] | true => #[b, a]) #[ty] (fun _ => true)
    let r ← MatchProg.operation (.llvm .add) (match rightCommuted with
      | false => #[a, d] | true => #[d, a]) #[ty] (fun _ => true)
    let _ ← MatchProg.root (.llvm .icmp) #[l.res[0]!, r.res[0]!] #[bt]
      (fun p => p.predicate = kind.pred)
    return (bt, b, d))
  (fun (bt, b, d) => do
    let cp ← CreateProg.property (.llvm .icmp) (IcmpProperties.mk kind.pred)
    CreateProg.operation (.llvm .icmp) #[b, d] #[bt] cp)
  (fun r => r.res[0]!)
private theorem pattern_valid (kind : EqNe) (lc rc : Bool) : Pattern.Valid (pattern kind lc rc) := by
  cases kind <;> cases lc <;> cases rc <;> simp only [pattern, EqNe.pred] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a b d lp lv hl; obtain rfl := (add_iff _ _ _ _ _).mp hl
    rintro rp rv hr; obtain rfl := (add_iff _ _ _ _ _).mp hr
    rintro cp cv hp hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    have hp' := of_decide_eq_true hp; rw [hp']
  · refine ⟨.int 1 (LLVM.Int.icmp b d .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_add_add_eq_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp b d .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags d a]
    simpa only [LLVM.Int.cast_self] using icmp_add_add_eq_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp b d .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags b a]
    simpa only [LLVM.Int.cast_self] using icmp_add_add_eq_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp b d .eq), (icmp_iff _ (IcmpProperties.mk .eq) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags b a, llvm_add_comm_flags d a]
    simpa only [LLVM.Int.cast_self] using icmp_add_add_eq_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp b d .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    simpa only [LLVM.Int.cast_self] using icmp_add_add_ne_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp b d .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags d a]
    simpa only [LLVM.Int.cast_self] using icmp_add_add_ne_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp b d .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags b a]
    simpa only [LLVM.Int.cast_self] using icmp_add_add_ne_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw
  · refine ⟨.int 1 (LLVM.Int.icmp b d .ne), (icmp_iff _ (IcmpProperties.mk .ne) _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    rw [llvm_add_comm_flags b a, llvm_add_comm_flags d a]
    simpa only [LLVM.Int.cast_self] using icmp_add_add_ne_flags a b d lp.nsw lp.nuw rp.nsw rp.nuw

public def addCompareAddEq : Pattern OpCode := pattern .eq false false
public theorem addCompareAddEq_valid : Pattern.Valid addCompareAddEq := pattern_valid .eq false false
public def addCompareAddEqRightCommuted : Pattern OpCode := pattern .eq false true
public theorem addCompareAddEqRightCommuted_valid : Pattern.Valid addCompareAddEqRightCommuted := pattern_valid .eq false true
public def addCompareAddEqLeftCommuted : Pattern OpCode := pattern .eq true false
public theorem addCompareAddEqLeftCommuted_valid : Pattern.Valid addCompareAddEqLeftCommuted := pattern_valid .eq true false
public def addCompareAddEqBothCommuted : Pattern OpCode := pattern .eq true true
public theorem addCompareAddEqBothCommuted_valid : Pattern.Valid addCompareAddEqBothCommuted := pattern_valid .eq true true
public def addCompareAddNe : Pattern OpCode := pattern .ne false false
public theorem addCompareAddNe_valid : Pattern.Valid addCompareAddNe := pattern_valid .ne false false
public def addCompareAddNeRightCommuted : Pattern OpCode := pattern .ne false true
public theorem addCompareAddNeRightCommuted_valid : Pattern.Valid addCompareAddNeRightCommuted := pattern_valid .ne false true
public def addCompareAddNeLeftCommuted : Pattern OpCode := pattern .ne true false
public theorem addCompareAddNeLeftCommuted_valid : Pattern.Valid addCompareAddNeLeftCommuted := pattern_valid .ne true false
public def addCompareAddNeBothCommuted : Pattern OpCode := pattern .ne true true
public theorem addCompareAddNeBothCommuted_valid : Pattern.Valid addCompareAddNeBothCommuted := pattern_valid .ne true true

private def guardedPattern (signed lc rc : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let d ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .add) (if lc then #[b, a] else #[a, b]) #[ty]
      (fun p => if signed then p.nsw else p.nuw)
    let r ← MatchProg.operation (.llvm .add) (if rc then #[d, a] else #[a, d]) #[ty]
      (fun p => if signed then p.nsw else p.nuw)
    let root ← MatchProg.root (.llvm .icmp) #[l.res[0]!, r.res[0]!] #[bt]
      (fun p => if signed then isSignedPredicate p.predicate else isUnsignedPredicate p.predicate)
    return (bt, b, d, root))
  (fun (bt, b, d, root) =>
    CreateProg.operation (.llvm .icmp) #[b, d] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem guardedPattern_valid (signed lc rc : Bool) : Pattern.Valid (guardedPattern signed lc rc) := by
  cases signed <;> cases lc <;> cases rc <;>
    simp only [guardedPattern, Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a b d lp lv hlf hl; obtain rfl := (add_iff _ _ _ _ _).mp hl
    rintro rp rv hrf hr; obtain rfl := (add_iff _ _ _ _ _).mp hr
    rintro cp cv hp hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    have hla : compareCancellationAllowed cp.predicate lp.nsw lp.nuw = true := by
      cases hpred : cp.predicate <;> simp_all [isSignedPredicate, isUnsignedPredicate,
        compareCancellationAllowed]
    have hra : compareCancellationAllowed cp.predicate rp.nsw rp.nuw = true := by
      cases hpred : cp.predicate <;> simp_all [isSignedPredicate, isUnsignedPredicate,
        compareCancellationAllowed]
    refine ⟨.int 1 (LLVM.Int.icmp b d cp.predicate), (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    first
    | exact (by simpa only [LLVM.Int.cast_self] using
        icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw rp.nsw rp.nuw hla hra)
    | (rw [llvm_add_comm_flags d a]
       exact (by simpa only [LLVM.Int.cast_self] using
         icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw rp.nsw rp.nuw hla hra))
    | (rw [llvm_add_comm_flags b a]
       exact (by simpa only [LLVM.Int.cast_self] using
         icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw rp.nsw rp.nuw hla hra))
    | (rw [llvm_add_comm_flags b a, llvm_add_comm_flags d a]
       exact (by simpa only [LLVM.Int.cast_self] using
         icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw rp.nsw rp.nuw hla hra))

public def addCompareAddUnsigned : Pattern OpCode := guardedPattern false false false
public theorem addCompareAddUnsigned_valid : Pattern.Valid addCompareAddUnsigned := guardedPattern_valid false false false
public def addCompareAddUnsignedRightCommuted : Pattern OpCode := guardedPattern false false true
public theorem addCompareAddUnsignedRightCommuted_valid : Pattern.Valid addCompareAddUnsignedRightCommuted := guardedPattern_valid false false true
public def addCompareAddUnsignedLeftCommuted : Pattern OpCode := guardedPattern false true false
public theorem addCompareAddUnsignedLeftCommuted_valid : Pattern.Valid addCompareAddUnsignedLeftCommuted := guardedPattern_valid false true false
public def addCompareAddUnsignedBothCommuted : Pattern OpCode := guardedPattern false true true
public theorem addCompareAddUnsignedBothCommuted_valid : Pattern.Valid addCompareAddUnsignedBothCommuted := guardedPattern_valid false true true
public def addCompareAddSigned : Pattern OpCode := guardedPattern true false false
public theorem addCompareAddSigned_valid : Pattern.Valid addCompareAddSigned := guardedPattern_valid true false false
public def addCompareAddSignedRightCommuted : Pattern OpCode := guardedPattern true false true
public theorem addCompareAddSignedRightCommuted_valid : Pattern.Valid addCompareAddSignedRightCommuted := guardedPattern_valid true false true
public def addCompareAddSignedLeftCommuted : Pattern OpCode := guardedPattern true true false
public theorem addCompareAddSignedLeftCommuted_valid : Pattern.Valid addCompareAddSignedLeftCommuted := guardedPattern_valid true true false
public def addCompareAddSignedBothCommuted : Pattern OpCode := guardedPattern true true true
public theorem addCompareAddSignedBothCommuted_valid : Pattern.Valid addCompareAddSignedBothCommuted := guardedPattern_valid true true true

private def orOrPattern (lc rc : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let d ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .or) (if lc then #[b, a] else #[a, b]) #[ty]
      (fun p => p.disjoint)
    let r ← MatchProg.operation (.llvm .or) (if rc then #[d, a] else #[a, d]) #[ty]
      (fun p => p.disjoint)
    let root ← MatchProg.root (.llvm .icmp) #[l.res[0]!, r.res[0]!] #[bt]
    return (bt, b, d, root))
  (fun (bt, b, d, root) =>
    CreateProg.operation (.llvm .icmp) #[b, d] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem orOrPattern_valid (lc rc : Bool) : Pattern.Valid (orOrPattern lc rc) := by
  cases lc <;> cases rc <;>
    simp only [orOrPattern, Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, HandleContext.lookup,
        HandleContext.lookupBindings, HandleContext.require, HandleContext.requireMany,
        HandleContext.insertFresh, HandleContext.insertManyFresh,
        MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a b d lp lv hld hl; obtain rfl := (or_iff _ lp _ _ _).mp hl
    rintro rp rv hrd hr; obtain rfl := (or_iff _ rp _ _ _).mp hr
    rintro (cp : IcmpProperties) cv hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    have hld' : lp.disjoint = true := hld; have hrd' : rp.disjoint = true := hrd
    rw [hld', hrd']
    refine ⟨.int 1 (LLVM.Int.icmp b d cp.predicate),
      (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    first
    | exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
        (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b)
          (disjoint_or_refines_add a d))
        (icmp_add_add_pred_flags cp.predicate a b d true true true true
          (by cases cp.predicate <;> rfl) (by cases cp.predicate <;> rfl))))
    | (rw [llvm_or_comm d a true]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b)
           (disjoint_or_refines_add a d))
         (icmp_add_add_pred_flags cp.predicate a b d true true true true
           (by cases cp.predicate <;> rfl) (by cases cp.predicate <;> rfl)))))
    | (rw [llvm_or_comm b a true]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b)
           (disjoint_or_refines_add a d))
         (icmp_add_add_pred_flags cp.predicate a b d true true true true
           (by cases cp.predicate <;> rfl) (by cases cp.predicate <;> rfl)))))
    | (rw [llvm_or_comm b a true, llvm_or_comm d a true]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b)
           (disjoint_or_refines_add a d))
         (icmp_add_add_pred_flags cp.predicate a b d true true true true
           (by cases cp.predicate <;> rfl) (by cases cp.predicate <;> rfl)))))

private def orAddPattern (lc rc : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let d ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .or) (if lc then #[b, a] else #[a, b]) #[ty]
      (fun p => p.disjoint)
    let r ← MatchProg.operation (.llvm .add) (if rc then #[d, a] else #[a, d]) #[ty]
      (fun _ => true)
    let root ← MatchProg.root (.llvm .icmp) #[l.res[0]!, r.res[0]!] #[bt]
    MatchProg.matchNative (root.properties, r.properties) fun (cp, rp) =>
      compareCancellationAllowed cp.predicate rp.nsw rp.nuw
    return (bt, b, d, root))
  (fun (bt, b, d, root) =>
    CreateProg.operation (.llvm .icmp) #[b, d] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem orAddPattern_valid (lc rc : Bool) : Pattern.Valid (orAddPattern lc rc) := by
  cases lc <;> cases rc <;>
    simp only [orAddPattern, Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a b d lp lv hld hl; obtain rfl := (or_iff _ lp _ _ _).mp hl
    rintro (rp : NswNuwProperties) rv hr; obtain rfl := (add_iff _ _ _ _ _).mp hr
    rintro (cp : IcmpProperties) cv hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    rintro hallowed
    have hld' : lp.disjoint = true := hld; rw [hld']
    refine ⟨.int 1 (LLVM.Int.icmp b d cp.predicate),
      (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    first
    | exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
        (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b) (isRefinedBy_refl _))
        (icmp_add_add_pred_flags cp.predicate a b d true true rp.nsw rp.nuw
          (by cases cp.predicate <;> rfl) hallowed)))
    | (rw [llvm_add_comm_flags d a]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b) (isRefinedBy_refl _))
         (icmp_add_add_pred_flags cp.predicate a b d true true rp.nsw rp.nuw
           (by cases cp.predicate <;> rfl) hallowed))))
    | (rw [llvm_or_comm b a true]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b) (isRefinedBy_refl _))
         (icmp_add_add_pred_flags cp.predicate a b d true true rp.nsw rp.nuw
           (by cases cp.predicate <;> rfl) hallowed))))
    | (rw [llvm_or_comm b a true, llvm_add_comm_flags d a]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (disjoint_or_refines_add a b) (isRefinedBy_refl _))
         (icmp_add_add_pred_flags cp.predicate a b d true true rp.nsw rp.nuw
           (by cases cp.predicate <;> rfl) hallowed))))

private def addOrPattern (lc rc : Bool) : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType)
    let bt ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty; let b ← MatchProg.value ty; let d ← MatchProg.value ty
    let l ← MatchProg.operation (.llvm .add) (if lc then #[b, a] else #[a, b]) #[ty]
      (fun _ => true)
    let r ← MatchProg.operation (.llvm .or) (if rc then #[d, a] else #[a, d]) #[ty]
      (fun p => p.disjoint)
    let root ← MatchProg.root (.llvm .icmp) #[l.res[0]!, r.res[0]!] #[bt]
    MatchProg.matchNative (root.properties, l.properties) fun (cp, lp) =>
      compareCancellationAllowed cp.predicate lp.nsw lp.nuw
    return (bt, b, d, root))
  (fun (bt, b, d, root) =>
    CreateProg.operation (.llvm .icmp) #[b, d] #[bt] root.properties)
  (fun r => r.res[0]!)

private theorem addOrPattern_valid (lc rc : Bool) : Pattern.Valid (addOrPattern lc rc) := by
  cases lc <;> cases rc <;>
    simp only [addOrPattern, Bool.false_eq_true, ite_false, ite_true] <;> unfoldPuddleBuilder
  all_goals
    constructor
    · provePuddleSupported
    · open scoped PuddleCbv in cbv
    · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit, MatchProg.collectBindings,
        MatchProg.collectDeclBindings, MatchProg.rootResults?, HandleContext.forbid,
        HandleContext.forbidMany, HandleContext.lookup, HandleContext.lookupBindings,
        HandleContext.require, HandleContext.requireMany, HandleContext.insertFresh,
        HandleContext.insertManyFresh, MetadataTuple.Shape.requireBindings,
        MetadataTuple.Shape.insertFreshBindings, IsMetadataTuple.shape_property,
        CreateProg.checkBindings, CreateDecl.checkBindings, Replacement.checkBindings]
    simpPuddleSemantics
    simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
    rintro ⟨w, s⟩ bt ⟨bw, bs⟩ hbt hbw; subst bt; change bw = 1 at hbw; subst bw
    rintro a b d (lp : NswNuwProperties) lv hl; obtain rfl := (add_iff _ _ _ _ _).mp hl
    rintro rp rv hrd hr; obtain rfl := (or_iff _ rp _ _ _).mp hr
    rintro (cp : IcmpProperties) cv hc; obtain rfl := (icmp_iff _ cp _ _ _).mp hc
    rintro hallowed
    have hrd' : rp.disjoint = true := hrd; rw [hrd']
    refine ⟨.int 1 (LLVM.Int.icmp b d cp.predicate),
      (icmp_iff _ cp _ _ _).mpr rfl, ⟨rfl, ?_⟩⟩
    first
    | exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
        (icmp_refine_mono cp.predicate (isRefinedBy_refl _) (disjoint_or_refines_add a d))
        (icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw true true
          hallowed (by cases cp.predicate <;> rfl))))
    | (rw [llvm_or_comm d a true]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (isRefinedBy_refl _) (disjoint_or_refines_add a d))
         (icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw true true
           hallowed (by cases cp.predicate <;> rfl)))))
    | (rw [llvm_add_comm_flags b a]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (isRefinedBy_refl _) (disjoint_or_refines_add a d))
         (icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw true true
           hallowed (by cases cp.predicate <;> rfl)))))
    | (rw [llvm_add_comm_flags b a, llvm_or_comm d a true]
       exact (by simpa only [LLVM.Int.cast_self] using (isRefinedBy_trans
         (icmp_refine_mono cp.predicate (isRefinedBy_refl _) (disjoint_or_refines_add a d))
         (icmp_add_add_pred_flags cp.predicate a b d lp.nsw lp.nuw true true
           hallowed (by cases cp.predicate <;> rfl)))))

public def orOrCompare : Pattern OpCode := orOrPattern false false
public theorem orOrCompare_valid : Pattern.Valid orOrCompare := orOrPattern_valid false false
public def orOrCompareRightCommuted : Pattern OpCode := orOrPattern false true
public theorem orOrCompareRightCommuted_valid : Pattern.Valid orOrCompareRightCommuted := orOrPattern_valid false true
public def orOrCompareLeftCommuted : Pattern OpCode := orOrPattern true false
public theorem orOrCompareLeftCommuted_valid : Pattern.Valid orOrCompareLeftCommuted := orOrPattern_valid true false
public def orOrCompareBothCommuted : Pattern OpCode := orOrPattern true true
public theorem orOrCompareBothCommuted_valid : Pattern.Valid orOrCompareBothCommuted := orOrPattern_valid true true
public def orAddCompare : Pattern OpCode := orAddPattern false false
public theorem orAddCompare_valid : Pattern.Valid orAddCompare := orAddPattern_valid false false
public def orAddCompareRightCommuted : Pattern OpCode := orAddPattern false true
public theorem orAddCompareRightCommuted_valid : Pattern.Valid orAddCompareRightCommuted := orAddPattern_valid false true
public def orAddCompareLeftCommuted : Pattern OpCode := orAddPattern true false
public theorem orAddCompareLeftCommuted_valid : Pattern.Valid orAddCompareLeftCommuted := orAddPattern_valid true false
public def orAddCompareBothCommuted : Pattern OpCode := orAddPattern true true
public theorem orAddCompareBothCommuted_valid : Pattern.Valid orAddCompareBothCommuted := orAddPattern_valid true true
public def addOrCompare : Pattern OpCode := addOrPattern false false
public theorem addOrCompare_valid : Pattern.Valid addOrCompare := addOrPattern_valid false false
public def addOrCompareRightCommuted : Pattern OpCode := addOrPattern false true
public theorem addOrCompareRightCommuted_valid : Pattern.Valid addOrCompareRightCommuted := addOrPattern_valid false true
public def addOrCompareLeftCommuted : Pattern OpCode := addOrPattern true false
public theorem addOrCompareLeftCommuted_valid : Pattern.Valid addOrCompareLeftCommuted := addOrPattern_valid true false
public def addOrCompareBothCommuted : Pattern OpCode := addOrPattern true true
public theorem addOrCompareBothCommuted_valid : Pattern.Valid addOrCompareBothCommuted := addOrPattern_valid true true
end Veir.Passes.InstCombineLLVM.AddCompareAdd
