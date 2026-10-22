import Veir.InstSimplify.IntrinsicSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS7413
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
def poison_bswap (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__bswap : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let result := LLVM.Int.bswap (.val (BitVec.ofInt it.bitwidth ai.value))
  return result.isPoison

def fold_bswap (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__bswap : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let result := LLVM.Int.bswap (.val (BitVec.ofInt it.bitwidth ai.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def bswap : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 16 || t.bitwidth == 32 || t.bitwidth == 64)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__bswap) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => !poison_bswap ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,a,rp) => do
    let p ← CreateProg.applyNative (ty,a,rp) (fun (ty,a,rp) => fold_bswap ty a rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem bswap_valid : Pattern.Valid bswap := by
  simp only [bswap]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (bswap_iff _ _ _ _).mp ri
  simp only [fold_bswap, TypeAttr.of_val, Attribute.of, ha]
  dsimp only [pure, Pure.pure]
  simp only [poison_bswap, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.bswap (.val (BitVec.ofInt w a.value))).isPoison = false at hn
  cases he : LLVM.Int.bswap (.val (BitVec.ofInt w a.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def bswap_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 16 || t.bitwidth == 32 || t.bitwidth == 64)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__bswap) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => poison_bswap ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem bswap_poison_valid : Pattern.Valid bswap_poison := by
  simp only [bswap_poison]
  provePuddleValid
  rintro _ ⟨w,s⟩ rfl hw ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (bswap_iff _ _ _ _).mp ri
  simp only [poison_bswap, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.bswap (.val (BitVec.ofInt w a.value))).isPoison = true at hn
  cases he : LLVM.Int.bswap (.val (BitVec.ofInt w a.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_bitreverse (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__bitreverse : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let result := LLVM.Int.bitreverse (.val (BitVec.ofInt it.bitwidth ai.value))
  return result.isPoison

def fold_bitreverse (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__bitreverse : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let result := LLVM.Int.bitreverse (.val (BitVec.ofInt it.bitwidth ai.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def bitreverse : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__bitreverse) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => !poison_bitreverse ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,a,rp) => do
    let p ← CreateProg.applyNative (ty,a,rp) (fun (ty,a,rp) => fold_bitreverse ty a rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem bitreverse_valid : Pattern.Valid bitreverse := by
  simp only [bitreverse]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (bitreverse_iff _ _ _ _).mp ri
  simp only [fold_bitreverse, TypeAttr.of_val, Attribute.of, ha]
  dsimp only [pure, Pure.pure]
  simp only [poison_bitreverse, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.bitreverse (.val (BitVec.ofInt w a.value))).isPoison = false at hn
  cases he : LLVM.Int.bitreverse (.val (BitVec.ofInt w a.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def bitreverse_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__bitreverse) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => poison_bitreverse ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem bitreverse_poison_valid : Pattern.Valid bitreverse_poison := by
  simp only [bitreverse_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (bitreverse_iff _ _ _ _).mp ri
  simp only [poison_bitreverse, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.bitreverse (.val (BitVec.ofInt w a.value))).isPoison = true at hn
  cases he : LLVM.Int.bitreverse (.val (BitVec.ofInt w a.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_ctpop (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ctpop : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let result := LLVM.Int.ctpop (.val (BitVec.ofInt it.bitwidth ai.value))
  return result.isPoison

def fold_ctpop (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ctpop : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let result := LLVM.Int.ctpop (.val (BitVec.ofInt it.bitwidth ai.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def ctpop : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ctpop) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => !poison_ctpop ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,a,rp) => do
    let p ← CreateProg.applyNative (ty,a,rp) (fun (ty,a,rp) => fold_ctpop ty a rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem ctpop_valid : Pattern.Valid ctpop := by
  simp only [ctpop]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (ctpop_iff _ _ _ _).mp ri
  simp only [fold_ctpop, TypeAttr.of_val, Attribute.of, ha]
  dsimp only [pure, Pure.pure]
  simp only [poison_ctpop, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.ctpop (.val (BitVec.ofInt w a.value))).isPoison = false at hn
  cases he : LLVM.Int.ctpop (.val (BitVec.ofInt w a.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def ctpop_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ctpop) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => poison_ctpop ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem ctpop_poison_valid : Pattern.Valid ctpop_poison := by
  simp only [ctpop_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (ctpop_iff _ _ _ _).mp ri
  simp only [poison_ctpop, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.ctpop (.val (BitVec.ofInt w a.value))).isPoison = true at hn
  cases he : LLVM.Int.ctpop (.val (BitVec.ofInt w a.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_ctlz (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ctlz : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let result := LLVM.Int.ctlz (.val (BitVec.ofInt it.bitwidth ai.value)) rp.is_zero_poison
  return result.isPoison

def fold_ctlz (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ctlz : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let result := LLVM.Int.ctlz (.val (BitVec.ofInt it.bitwidth ai.value)) rp.is_zero_poison
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def ctlz : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ctlz) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => !poison_ctlz ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,a,rp) => do
    let p ← CreateProg.applyNative (ty,a,rp) (fun (ty,a,rp) => fold_ctlz ty a rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem ctlz_valid : Pattern.Valid ctlz := by
  simp only [ctlz]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (ctlz_iff _ _ _ _).mp ri
  simp only [fold_ctlz, TypeAttr.of_val, Attribute.of, ha]
  dsimp only [pure, Pure.pure]
  simp only [poison_ctlz, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.ctlz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison).isPoison = false at hn
  cases he : LLVM.Int.ctlz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def ctlz_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ctlz) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => poison_ctlz ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem ctlz_poison_valid : Pattern.Valid ctlz_poison := by
  simp only [ctlz_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (ctlz_iff _ _ _ _).mp ri
  simp only [poison_ctlz, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.ctlz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison).isPoison = true at hn
  cases he : LLVM.Int.ctlz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_cttz (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__cttz : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let result := LLVM.Int.cttz (.val (BitVec.ofInt it.bitwidth ai.value)) rp.is_zero_poison
  return result.isPoison

def fold_cttz (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__cttz : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let result := LLVM.Int.cttz (.val (BitVec.ofInt it.bitwidth ai.value)) rp.is_zero_poison
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def cttz : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__cttz) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => !poison_cttz ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,a,rp) => do
    let p ← CreateProg.applyNative (ty,a,rp) (fun (ty,a,rp) => fold_cttz ty a rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem cttz_valid : Pattern.Valid cttz := by
  simp only [cttz]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (cttz_iff _ _ _ _).mp ri
  simp only [fold_cttz, TypeAttr.of_val, Attribute.of, ha]
  dsimp only [pure, Pure.pure]
  simp only [poison_cttz, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.cttz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison).isPoison = false at hn
  cases he : LLVM.Int.cttz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def cttz_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__cttz) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => poison_cttz ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem cttz_poison_valid : Pattern.Valid cttz_poison := by
  simp only [cttz_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (cttz_iff _ _ _ _).mp ri
  simp only [poison_cttz, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.cttz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison).isPoison = true at hn
  cases he : LLVM.Int.cttz (.val (BitVec.ofInt w a.value)) rp.is_zero_poison with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_abs (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__abs : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let result := LLVM.Int.abs (.val (BitVec.ofInt it.bitwidth ai.value)) rp.is_int_min_poison
  return result.isPoison

def fold_abs (t : TypeAttr) (a : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__abs : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let result := LLVM.Int.abs (.val (BitVec.ofInt it.bitwidth ai.value)) rp.is_int_min_poison
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def abs : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__abs) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => !poison_abs ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,a,rp) => do
    let p ← CreateProg.applyNative (ty,a,rp) (fun (ty,a,rp) => fold_abs ty a rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem abs_valid : Pattern.Valid abs := by
  simp only [abs]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (abs_iff _ _ _ _).mp ri
  simp only [fold_abs, TypeAttr.of_val, Attribute.of, ha]
  dsimp only [pure, Pure.pure]
  simp only [poison_abs, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.abs (.val (BitVec.ofInt w a.value)) rp.is_int_min_poison).isPoison = false at hn
  cases he : LLVM.Int.abs (.val (BitVec.ofInt w a.value)) rp.is_int_min_poison with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def abs_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__abs) #[a.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,r.properties) (fun (ty,a,rp) => poison_abs ty a rp)
    return (ty,a.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem abs_poison_valid : Pattern.Valid abs_poison := by
  simp only [abs_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain rfl := (abs_iff _ _ _ _).mp ri
  simp only [poison_abs, TypeAttr.of_val, Attribute.of, ha] at hn
  change (LLVM.Int.abs (.val (BitVec.ofInt w a.value)) rp.is_int_min_poison).isPoison = true at hn
  cases he : LLVM.Int.abs (.val (BitVec.ofInt w a.value)) rp.is_int_min_poison with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_smax (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__smax : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.smax (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_smax (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__smax : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.smax (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def smax : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__smax) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_smax ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_smax ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem smax_valid : Pattern.Valid smax := by
  simp only [smax]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (smax_iff _ _ _ _ _).mp ri
  simp only [fold_smax, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_smax, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.smax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.smax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def smax_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__smax) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_smax ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem smax_poison_valid : Pattern.Valid smax_poison := by
  simp only [smax_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (smax_iff _ _ _ _ _).mp ri
  simp only [poison_smax, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.smax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.smax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_smin (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__smin : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.smin (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_smin (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__smin : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.smin (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def smin : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__smin) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_smin ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_smin ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem smin_valid : Pattern.Valid smin := by
  simp only [smin]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (smin_iff _ _ _ _ _).mp ri
  simp only [fold_smin, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_smin, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.smin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.smin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def smin_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__smin) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_smin ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem smin_poison_valid : Pattern.Valid smin_poison := by
  simp only [smin_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (smin_iff _ _ _ _ _).mp ri
  simp only [poison_smin, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.smin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.smin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_umax (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__umax : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.umax (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_umax (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__umax : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.umax (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def umax : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__umax) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_umax ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_umax ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem umax_valid : Pattern.Valid umax := by
  simp only [umax]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (umax_iff _ _ _ _ _).mp ri
  simp only [fold_umax, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_umax, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.umax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.umax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def umax_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__umax) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_umax ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem umax_poison_valid : Pattern.Valid umax_poison := by
  simp only [umax_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (umax_iff _ _ _ _ _).mp ri
  simp only [poison_umax, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.umax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.umax (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_umin (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__umin : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.umin (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_umin (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__umin : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.umin (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def umin : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__umin) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_umin ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_umin ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem umin_valid : Pattern.Valid umin := by
  simp only [umin]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (umin_iff _ _ _ _ _).mp ri
  simp only [fold_umin, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_umin, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.umin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.umin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def umin_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__umin) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_umin ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem umin_poison_valid : Pattern.Valid umin_poison := by
  simp only [umin_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (umin_iff _ _ _ _ _).mp ri
  simp only [poison_umin, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.umin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.umin (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_saddSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__sadd__sat : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.saddSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_saddSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__sadd__sat : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.saddSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def saddSat : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__sadd__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_saddSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_saddSat ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem saddSat_valid : Pattern.Valid saddSat := by
  simp only [saddSat]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (saddSat_iff _ _ _ _ _).mp ri
  simp only [fold_saddSat, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_saddSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.saddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.saddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def saddSat_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__sadd__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_saddSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem saddSat_poison_valid : Pattern.Valid saddSat_poison := by
  simp only [saddSat_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (saddSat_iff _ _ _ _ _).mp ri
  simp only [poison_saddSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.saddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.saddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_uaddSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__uadd__sat : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.uaddSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_uaddSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__uadd__sat : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.uaddSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def uaddSat : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__uadd__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_uaddSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_uaddSat ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem uaddSat_valid : Pattern.Valid uaddSat := by
  simp only [uaddSat]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (uaddSat_iff _ _ _ _ _).mp ri
  simp only [fold_uaddSat, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_uaddSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.uaddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.uaddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def uaddSat_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__uadd__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_uaddSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem uaddSat_poison_valid : Pattern.Valid uaddSat_poison := by
  simp only [uaddSat_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (uaddSat_iff _ _ _ _ _).mp ri
  simp only [poison_uaddSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.uaddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.uaddSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_ssubSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ssub__sat : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.ssubSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_ssubSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ssub__sat : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.ssubSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def ssubSat : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ssub__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_ssubSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_ssubSat ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem ssubSat_valid : Pattern.Valid ssubSat := by
  simp only [ssubSat]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (ssubSat_iff _ _ _ _ _).mp ri
  simp only [fold_ssubSat, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_ssubSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.ssubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.ssubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def ssubSat_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ssub__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_ssubSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem ssubSat_poison_valid : Pattern.Valid ssubSat_poison := by
  simp only [ssubSat_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (ssubSat_iff _ _ _ _ _).mp ri
  simp only [poison_ssubSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.ssubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.ssubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_usubSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__usub__sat : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.usubSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_usubSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__usub__sat : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.usubSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def usubSat : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__usub__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_usubSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_usubSat ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem usubSat_valid : Pattern.Valid usubSat := by
  simp only [usubSat]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (usubSat_iff _ _ _ _ _).mp ri
  simp only [fold_usubSat, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_usubSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.usubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.usubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def usubSat_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__usub__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_usubSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem usubSat_poison_valid : Pattern.Valid usubSat_poison := by
  simp only [usubSat_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (usubSat_iff _ _ _ _ _).mp ri
  simp only [poison_usubSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.usubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.usubSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_sshlSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__sshl__sat : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.sshlSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_sshlSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__sshl__sat : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.sshlSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def sshlSat : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__sshl__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_sshlSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_sshlSat ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem sshlSat_valid : Pattern.Valid sshlSat := by
  simp only [sshlSat]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (sshlSat_iff _ _ _ _ _).mp ri
  simp only [fold_sshlSat, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_sshlSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.sshlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.sshlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def sshlSat_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__sshl__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_sshlSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem sshlSat_poison_valid : Pattern.Valid sshlSat_poison := by
  simp only [sshlSat_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (sshlSat_iff _ _ _ _ _).mp ri
  simp only [poison_sshlSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.sshlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.sshlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_ushlSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ushl__sat : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let result := LLVM.Int.ushlSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return result.isPoison

def fold_ushlSat (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__ushl__sat : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let result := LLVM.Int.ushlSat (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def ushlSat : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ushl__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => !poison_ushlSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,a,b,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,rp) (fun (ty,a,b,rp) => fold_ushlSat ty a b rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem ushlSat_valid : Pattern.Valid ushlSat := by
  simp only [ushlSat]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (ushlSat_iff _ _ _ _ _).mp ri
  simp only [fold_ushlSat, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  simp only [poison_ushlSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.ushlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = false at hn
  cases he : LLVM.Int.ushlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def ushlSat_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__ushl__sat) #[a.res[0]!,b.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,r.properties) (fun (ty,a,b,rp) => poison_ushlSat ty a b rp)
    return (ty,a.properties,b.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem ushlSat_poison_valid : Pattern.Valid ushlSat_poison := by
  simp only [ushlSat_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain rfl := (ushlSat_iff _ _ _ _ _).mp ri
  simp only [poison_ushlSat, TypeAttr.of_val, Attribute.of, ha, hb] at hn
  change (LLVM.Int.ushlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value))).isPoison = true at hn
  cases he : LLVM.Int.ushlSat (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_fshl (t : TypeAttr) (a b c : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__fshl : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let .integer ci := c.value | false
  let result := LLVM.Int.fshl (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value)) (.val (BitVec.ofInt it.bitwidth ci.value))
  return result.isPoison

def fold_fshl (t : TypeAttr) (a b c : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__fshl : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let .integer ci := c.value | none
  let result := LLVM.Int.fshl (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value)) (.val (BitVec.ofInt it.bitwidth ci.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def fshl : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__fshl) #[a.res[0]!,b.res[0]!,c.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,c.properties,r.properties) (fun (ty,a,b,c,rp) => !poison_fshl ty a b c rp)
    return (ty,a.properties,b.properties,c.properties,r.properties))
  (fun (ty,a,b,c,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,c,rp) (fun (ty,a,b,c,rp) => fold_fshl ty a b c rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem fshl_valid : Pattern.Valid fshl := by
  simp only [fshl]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh cp cv ch rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain ⟨c,hc,rfl⟩ := intrinsic_constant_success _ cp cv ch
  obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
  simp only [fold_fshl, TypeAttr.of_val, Attribute.of, ha, hb, hc]
  dsimp only [pure, Pure.pure]
  simp only [poison_fshl, TypeAttr.of_val, Attribute.of, ha, hb, hc] at hn
  change (LLVM.Int.fshl (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value))).isPoison = false at hn
  cases he : LLVM.Int.fshl (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
def fshl_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__fshl) #[a.res[0]!,b.res[0]!,c.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,c.properties,r.properties) (fun (ty,a,b,c,rp) => poison_fshl ty a b c rp)
    return (ty,a.properties,b.properties,c.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem fshl_poison_valid : Pattern.Valid fshl_poison := by
  simp only [fshl_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh cp cv ch rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain ⟨c,hc,rfl⟩ := intrinsic_constant_success _ cp cv ch
  obtain rfl := (fshl_iff _ _ _ _ _ _).mp ri
  simp only [poison_fshl, TypeAttr.of_val, Attribute.of, ha, hb, hc] at hn
  change (LLVM.Int.fshl (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value))).isPoison = true at hn
  cases he : LLVM.Int.fshl (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

def poison_fshr (t : TypeAttr) (a b c : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__fshr : OpCode)) : Bool := Id.run do
  let .integerType it := t.val | false
  let .integer ai := a.value | false
  let .integer bi := b.value | false
  let .integer ci := c.value | false
  let result := LLVM.Int.fshr (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value)) (.val (BitVec.ofInt it.bitwidth ci.value))
  return result.isPoison

def fold_fshr (t : TypeAttr) (a b c : propertiesOf (.llvm .mlir__constant : OpCode))
    (rp : propertiesOf (.llvm .intr__fshr : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let .integer ci := c.value | none
  let result := LLVM.Int.fshr (.val (BitVec.ofInt it.bitwidth ai.value)) (.val (BitVec.ofInt it.bitwidth bi.value)) (.val (BitVec.ofInt it.bitwidth ci.value))
  return {value := .integer {type := it, value := (intrinsic_result_bits result).toInt}}

def fshr : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__fshr) #[a.res[0]!,b.res[0]!,c.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,c.properties,r.properties) (fun (ty,a,b,c,rp) => !poison_fshr ty a b c rp)
    return (ty,a.properties,b.properties,c.properties,r.properties))
  (fun (ty,a,b,c,rp) => do
    let p ← CreateProg.applyNative (ty,a,b,c,rp) (fun (ty,a,b,c,rp) => fold_fshr ty a b c rp)
    CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
  (fun r => r)

theorem fshr_valid : Pattern.Valid fshr := by
  simp only [fshr]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh cp cv ch rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain ⟨c,hc,rfl⟩ := intrinsic_constant_success _ cp cv ch
  obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
  simp only [fold_fshr, TypeAttr.of_val, Attribute.of, ha, hb, hc]
  dsimp only [pure, Pure.pure]
  simp only [poison_fshr, TypeAttr.of_val, Attribute.of, ha, hb, hc] at hn
  change (LLVM.Int.fshr (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value))).isPoison = false at hn
  cases he : LLVM.Int.fshr (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value)) with
  | poison => simp [he, LLVM.Int.isPoison] at hn
  | val r =>
    refine ⟨.int w (.val r), ?_, ?_⟩
    · exact (constant_iff _ _ _ rfl _).mpr (by simp [intrinsic_result_bits, he])
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]

def fshr_poison : Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun _ => true)
    let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
    let r ← MatchProg.root (.llvm .intr__fshr) #[a.res[0]!,b.res[0]!,c.res[0]!] #[ty]
    MatchProg.matchNative (ty,a.properties,b.properties,c.properties,r.properties) (fun (ty,a,b,c,rp) => poison_fshr ty a b c rp)
    return (ty,a.properties,b.properties,c.properties,r.properties))
  (fun (ty,_) => do
    let p ← CreateProg.property (.llvm .mlir__poison) ()
    CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
  (fun r => r)

theorem fshr_poison_valid : Pattern.Valid fshr_poison := by
  simp only [fshr_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ah bp bv bh cp cv ch rp rv ri hn
  obtain ⟨a,ha,rfl⟩ := intrinsic_constant_success _ ap av ah
  obtain ⟨b,hb,rfl⟩ := intrinsic_constant_success _ bp bv bh
  obtain ⟨c,hc,rfl⟩ := intrinsic_constant_success _ cp cv ch
  obtain rfl := (fshr_iff _ _ _ _ _ _).mp ri
  simp only [poison_fshr, TypeAttr.of_val, Attribute.of, ha, hb, hc] at hn
  change (LLVM.Int.fshr (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value))).isPoison = true at hn
  cases he : LLVM.Int.fshr (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) (.val (BitVec.ofInt w c.value)) with
  | poison =>
    refine ⟨.int w .poison, ?_, ?_⟩
    · exact (poison_iff _ _ _).mpr rfl
    · simp [he, RuntimeValue.isRefinedBy, isRefinedBy]
  | val r => simp [he, LLVM.Int.isPoison] at hn

end Veir.InstSimplify.IS7413
