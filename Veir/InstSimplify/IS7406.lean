import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS7406
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Poison propagation for actual modeled LLVM bswap, operand 0. -/
def bswap_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 16 || t.bitwidth == 32 || t.bitwidth == 64)
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__bswap) #[p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem bswap_0_valid : Pattern.Valid bswap_0 := by
  simp only [bswap_0]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (bswap_iff _ _ _ _).mp ri
  simp [LLVM.Int.bswap, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM bitreverse, operand 0. -/
def bitreverse_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__bitreverse) #[p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem bitreverse_0_valid : Pattern.Valid bitreverse_0 := by
  simp only [bitreverse_0]
  provePuddleValid
  rintro ⟨w,s⟩
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (bitreverse_iff _ _ _ _).mp ri
  simp [LLVM.Int.bitreverse, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM ctpop, operand 0. -/
def ctpop_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ctpop) #[p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem ctpop_0_valid : Pattern.Valid ctpop_0 := by
  simp only [ctpop_0]
  provePuddleValid
  rintro ⟨w,s⟩
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (ctpop_iff _ _ _ _).mp ri
  simp [LLVM.Int.ctpop, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM ctlz, operand 0. -/
def ctlz_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ctlz) #[p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem ctlz_0_valid : Pattern.Valid ctlz_0 := by
  simp only [ctlz_0]
  provePuddleValid
  rintro ⟨w,s⟩
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (ctlz_iff _ _ _ _).mp ri
  simp [LLVM.Int.ctlz, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM cttz, operand 0. -/
def cttz_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__cttz) #[p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem cttz_0_valid : Pattern.Valid cttz_0 := by
  simp only [cttz_0]
  provePuddleValid
  rintro ⟨w,s⟩
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (cttz_iff _ _ _ _).mp ri
  simp [LLVM.Int.cttz, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM abs, operand 0. -/
def abs_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__abs) #[p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem abs_0_valid : Pattern.Valid abs_0 := by
  simp only [abs_0]
  provePuddleValid
  rintro ⟨w,s⟩
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (abs_iff _ _ _ _).mp ri
  simp [LLVM.Int.abs, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM smax, operand 0. -/
def smax_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__smax) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem smax_0_valid : Pattern.Valid smax_0 := by
  simp only [smax_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (smax_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.smax, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM smax, operand 1. -/
def smax_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__smax) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem smax_1_valid : Pattern.Valid smax_1 := by
  simp only [smax_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (smax_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.smax, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM smin, operand 0. -/
def smin_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__smin) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem smin_0_valid : Pattern.Valid smin_0 := by
  simp only [smin_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (smin_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.smin, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM smin, operand 1. -/
def smin_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__smin) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem smin_1_valid : Pattern.Valid smin_1 := by
  simp only [smin_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (smin_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.smin, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM umax, operand 0. -/
def umax_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__umax) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem umax_0_valid : Pattern.Valid umax_0 := by
  simp only [umax_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (umax_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.umax, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM umax, operand 1. -/
def umax_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__umax) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem umax_1_valid : Pattern.Valid umax_1 := by
  simp only [umax_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (umax_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.umax, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM umin, operand 0. -/
def umin_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__umin) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem umin_0_valid : Pattern.Valid umin_0 := by
  simp only [umin_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (umin_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.umin, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM umin, operand 1. -/
def umin_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__umin) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem umin_1_valid : Pattern.Valid umin_1 := by
  simp only [umin_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (umin_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.umin, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM sadd__sat, operand 0. -/
def saddSat_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__sadd__sat) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem saddSat_0_valid : Pattern.Valid saddSat_0 := by
  simp only [saddSat_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (saddSat_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.saddSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM sadd__sat, operand 1. -/
def saddSat_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__sadd__sat) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem saddSat_1_valid : Pattern.Valid saddSat_1 := by
  simp only [saddSat_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (saddSat_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.saddSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM uadd__sat, operand 0. -/
def uaddSat_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__uadd__sat) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem uaddSat_0_valid : Pattern.Valid uaddSat_0 := by
  simp only [uaddSat_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (uaddSat_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.uaddSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM uadd__sat, operand 1. -/
def uaddSat_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__uadd__sat) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem uaddSat_1_valid : Pattern.Valid uaddSat_1 := by
  simp only [uaddSat_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (uaddSat_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.uaddSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM ssub__sat, operand 0. -/
def ssubSat_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ssub__sat) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem ssubSat_0_valid : Pattern.Valid ssubSat_0 := by
  simp only [ssubSat_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (ssubSat_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.ssubSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM ssub__sat, operand 1. -/
def ssubSat_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ssub__sat) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem ssubSat_1_valid : Pattern.Valid ssubSat_1 := by
  simp only [ssubSat_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (ssubSat_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.ssubSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM usub__sat, operand 0. -/
def usubSat_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__usub__sat) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem usubSat_0_valid : Pattern.Valid usubSat_0 := by
  simp only [usubSat_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (usubSat_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.usubSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM usub__sat, operand 1. -/
def usubSat_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__usub__sat) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem usubSat_1_valid : Pattern.Valid usubSat_1 := by
  simp only [usubSat_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (usubSat_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.usubSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM sshl__sat, operand 0. -/
def sshlSat_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__sshl__sat) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem sshlSat_0_valid : Pattern.Valid sshlSat_0 := by
  simp only [sshlSat_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (sshlSat_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.sshlSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM sshl__sat, operand 1. -/
def sshlSat_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__sshl__sat) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem sshlSat_1_valid : Pattern.Valid sshlSat_1 := by
  simp only [sshlSat_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (sshlSat_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.sshlSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM ushl__sat, operand 0. -/
def ushlSat_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ushl__sat) #[p.res[0]!,x1] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem ushlSat_0_valid : Pattern.Valid ushlSat_0 := by
  simp only [ushlSat_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (ushlSat_iff _ _ _ _ _).mp ri
  cases x1
  all_goals
    simp [LLVM.Int.ushlSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM ushl__sat, operand 1. -/
def ushlSat_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__ushl__sat) #[x0,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem ushlSat_1_valid : Pattern.Valid ushlSat_1 := by
  simp only [ushlSat_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (ushlSat_iff _ _ _ _ _).mp ri
  cases x0
  all_goals
    simp [LLVM.Int.ushlSat, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM fshl, operand 0. -/
def fshl_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let x2 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__fshl) #[p.res[0]!,x1,x2] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem fshl_0_valid : Pattern.Valid fshl_0 := by
  simp only [fshl_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1 x2
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
  cases x1 <;> cases x2
  all_goals
    simp [LLVM.Int.fshl, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM fshl, operand 1. -/
def fshl_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let x2 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__fshl) #[x0,p.res[0]!,x2] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem fshl_1_valid : Pattern.Valid fshl_1 := by
  simp only [fshl_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0 x2
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
  cases x0 <;> cases x2
  all_goals
    simp [LLVM.Int.fshl, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM fshl, operand 2. -/
def fshl_2 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__fshl) #[x0,x1,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem fshl_2_valid : Pattern.Valid fshl_2 := by
  simp only [fshl_2]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0 x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
  cases x0 <;> cases x1
  all_goals
    simp [LLVM.Int.fshl, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM fshr, operand 0. -/
def fshr_0 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x1 ← MatchProg.value ty
    let x2 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__fshr) #[p.res[0]!,x1,x2] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem fshr_0_valid : Pattern.Valid fshr_0 := by
  simp only [fshr_0]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x1 x2
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
  cases x1 <;> cases x2
  all_goals
    simp [LLVM.Int.fshr, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM fshr, operand 1. -/
def fshr_1 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let x2 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__fshr) #[x0,p.res[0]!,x2] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem fshr_1_valid : Pattern.Valid fshr_1 := by
  simp only [fshr_1]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0 x2
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
  cases x0 <;> cases x2
  all_goals
    simp [LLVM.Int.fshr, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]

/-- Poison propagation for actual modeled LLVM fshr, operand 2. -/
def fshr_2 : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let x0 ← MatchProg.value ty
    let x1 ← MatchProg.value ty
    let p ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
    let _ ← MatchProg.root (.llvm .intr__fshr) #[x0,x1,p.res[0]!] #[ty]
    return p.res[0]!)
  pure (fun x => x)
theorem fshr_2_valid : Pattern.Valid fshr_2 := by
  simp only [fshr_2]
  provePuddleValid
  rintro ⟨w,s⟩
  simp only [RuntimeValue.Conforms.integerType, forall_exists_index, forall_eq_apply_imp_iff]
  intro x0 x1
  rintro pp pv pi rp rv ri
  obtain rfl := (poison_iff _ _ _).mp pi
  obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
  cases x0 <;> cases x1
  all_goals
    simp [LLVM.Int.fshr, LLVM.Int.mlir_poison, RuntimeValue.isRefinedBy, isRefinedBy, Id.run, pure]
end Veir.InstSimplify.IS7406
