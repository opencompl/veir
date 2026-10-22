import Veir.InstSimplify.ArithmeticSupport
open Veir Veir.Puddle Veir.Data
namespace Veir.InstSimplify.IS0582

private theorem constant_success (ty : IntegerType) (p : propertiesOf (.llvm .mlir__constant : OpCode))
    (v : RuntimeValue) (h : InterpretsTo (.llvm .mlir__constant) p #[ty] #[] #[v]) :
    ∃ a : IntegerAttr, p.value = .integer a ∧
      v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth a.value)) := by
  cases ty
  cases hp : p.value with
  | integer a => exact ⟨a, rfl, (constant_iff _ p a hp v).mp h⟩
  | float a =>
    simp [InterpretsTo, interpretOp', Llvm.interpretOp', hp, TypeAttr.of_val,
      Attribute.of, -Attribute.integerType_eq_of] at h
    exact False.elim (h.2 MemoryState.empty)
  | dense a =>
    simp [InterpretsTo, interpretOp', Llvm.interpretOp', hp, TypeAttr.of_val,
      Attribute.of, -Attribute.integerType_eq_of] at h
    exact False.elim (h.2 MemoryState.empty)
  | string a =>
    simp [InterpretsTo, interpretOp', Llvm.interpretOp', hp, TypeAttr.of_val,
      Attribute.of, -Attribute.integerType_eq_of] at h
    exact False.elim (h.2 MemoryState.empty)

private def fold_add (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x + y).toInt}}

def pattern_add : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .add) #[a.res[0]!, b.res[0]!] #[ty]
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_add ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_add_valid : Pattern.Valid pattern_add := by
  simp only [pattern_add]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (add_iff w rp _ _ rv).mp ri
  simp only [fold_add, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x + y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.add, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def fold_sub (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x - y).toInt}}

def pattern_sub : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .sub) #[a.res[0]!, b.res[0]!] #[ty]
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_sub ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_sub_valid : Pattern.Valid pattern_sub := by
  simp only [pattern_sub]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (sub_iff w rp _ _ rv).mp ri
  simp only [fold_sub, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x - y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.sub, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def fold_mul (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x * y).toInt}}

def pattern_mul : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .mul) #[a.res[0]!, b.res[0]!] #[ty]
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_mul ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_mul_valid : Pattern.Valid pattern_mul := by
  simp only [pattern_mul]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (mul_iff w rp _ _ rv).mp ri
  simp only [fold_mul, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x * y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.mul, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def constantDefined_shl (t : TypeAttr)
    (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Bool :=
  match t.val, a.value, b.value with
  | .integerType it, .integer ai, .integer bi =>
    let x := BitVec.ofInt it.bitwidth ai.value
    let y := BitVec.ofInt it.bitwidth bi.value
    decide (y.toNat < it.bitwidth)
  | _,_,_ => false

private def fold_shl (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x <<< y).toInt}}

def pattern_shl : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .shl) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => constantDefined_shl ty a b)
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_shl ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_shl_valid : Pattern.Valid pattern_shl := by
  simp only [pattern_shl]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hdefined
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (shl_iff w rp _ _ rv).mp ri
  simp only [fold_shl, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x <<< y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.shl, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def constantDefined_lshr (t : TypeAttr)
    (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Bool :=
  match t.val, a.value, b.value with
  | .integerType it, .integer ai, .integer bi =>
    let x := BitVec.ofInt it.bitwidth ai.value
    let y := BitVec.ofInt it.bitwidth bi.value
    decide (y.toNat < it.bitwidth)
  | _,_,_ => false

private def fold_lshr (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x >>> y).toInt}}

def pattern_lshr : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .lshr) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => constantDefined_lshr ty a b)
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_lshr ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_lshr_valid : Pattern.Valid pattern_lshr := by
  simp only [pattern_lshr]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hdefined
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (lshr_iff w rp _ _ rv).mp ri
  simp only [fold_lshr, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x >>> y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.lshr, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def constantDefined_ashr (t : TypeAttr)
    (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Bool :=
  match t.val, a.value, b.value with
  | .integerType it, .integer ai, .integer bi =>
    let x := BitVec.ofInt it.bitwidth ai.value
    let y := BitVec.ofInt it.bitwidth bi.value
    decide (y.toNat < it.bitwidth)
  | _,_,_ => false

private def fold_ashr (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x.sshiftRight' y).toInt}}

def pattern_ashr : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .ashr) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => constantDefined_ashr ty a b)
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_ashr ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_ashr_valid : Pattern.Valid pattern_ashr := by
  simp only [pattern_ashr]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hdefined
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (ashr_iff w rp _ _ rv).mp ri
  simp only [fold_ashr, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x.sshiftRight' y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.ashr, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def fold_and (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x &&& y).toInt}}

def pattern_and : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .and) #[a.res[0]!, b.res[0]!] #[ty]
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_and ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_and_valid : Pattern.Valid pattern_and := by
  simp only [pattern_and]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (and_iff w rp _ _ rv).mp ri
  simp only [fold_and, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x &&& y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.and, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def fold_or (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x ||| y).toInt}}

def pattern_or : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .or) #[a.res[0]!, b.res[0]!] #[ty]
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_or ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_or_valid : Pattern.Valid pattern_or := by
  simp only [pattern_or]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (or_iff w rp _ _ rv).mp ri
  simp only [fold_or, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x ||| y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.or, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def fold_xor (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x ^^^ y).toInt}}

def pattern_xor : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .xor) #[a.res[0]!, b.res[0]!] #[ty]
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_xor ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_xor_valid : Pattern.Valid pattern_xor := by
  simp only [pattern_xor]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (xor_iff w rp _ _ rv).mp ri
  simp only [fold_xor, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x ^^^ y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.xor, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def constantDefined_udiv (t : TypeAttr)
    (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Bool :=
  match t.val, a.value, b.value with
  | .integerType it, .integer ai, .integer bi =>
    let x := BitVec.ofInt it.bitwidth ai.value
    let y := BitVec.ofInt it.bitwidth bi.value
    !(LLVM.Int.isUnsignedDivisionUB (.val y))
  | _,_,_ => false

private def fold_udiv (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x / y).toInt}}

def pattern_udiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .udiv) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => constantDefined_udiv ty a b)
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_udiv ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_udiv_valid : Pattern.Valid pattern_udiv := by
  simp only [pattern_udiv]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hdefined
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (udiv_iff w rp _ _ rv).mp ri
  simp only [fold_udiv, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x / y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.udiv, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def constantDefined_sdiv (t : TypeAttr)
    (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Bool :=
  match t.val, a.value, b.value with
  | .integerType it, .integer ai, .integer bi =>
    let x := BitVec.ofInt it.bitwidth ai.value
    let y := BitVec.ofInt it.bitwidth bi.value
    !(LLVM.Int.isSignedDivisionUB (.val x) (.val y))
  | _,_,_ => false

private def fold_sdiv (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x.sdiv y).toInt}}

def pattern_sdiv : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .sdiv) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => constantDefined_sdiv ty a b)
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_sdiv ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_sdiv_valid : Pattern.Valid pattern_sdiv := by
  simp only [pattern_sdiv]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hdefined
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (sdiv_iff w rp _ _ rv).mp ri
  simp only [fold_sdiv, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x.sdiv y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.sdiv, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def constantDefined_urem (t : TypeAttr)
    (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Bool :=
  match t.val, a.value, b.value with
  | .integerType it, .integer ai, .integer bi =>
    let x := BitVec.ofInt it.bitwidth ai.value
    let y := BitVec.ofInt it.bitwidth bi.value
    !(LLVM.Int.isUnsignedDivisionUB (.val y))
  | _,_,_ => false

private def fold_urem (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x % y).toInt}}

def pattern_urem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .urem) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => constantDefined_urem ty a b)
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_urem ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_urem_valid : Pattern.Valid pattern_urem := by
  simp only [pattern_urem]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hdefined
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (urem_iff w rp _ _ rv).mp ri
  simp only [fold_urem, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x % y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.urem, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

private def constantDefined_srem (t : TypeAttr)
    (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Bool :=
  match t.val, a.value, b.value with
  | .integerType it, .integer ai, .integer bi =>
    let x := BitVec.ofInt it.bitwidth ai.value
    let y := BitVec.ofInt it.bitwidth bi.value
    !(LLVM.Int.isSignedDivisionUB (.val x) (.val y))
  | _,_,_ => false

private def fold_srem (t : TypeAttr) (a b : propertiesOf (.llvm .mlir__constant : OpCode)) : Option (propertiesOf (.llvm .mlir__constant : OpCode)) := do
  let .integerType it := t.val | none
  let .integer ai := a.value | none
  let .integer bi := b.value | none
  let x := BitVec.ofInt it.bitwidth ai.value
  let y := BitVec.ofInt it.bitwidth bi.value
  return {value := .integer {type := it, value := (x.srem y).toInt}}

def pattern_srem : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .srem) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => constantDefined_srem ty a b)
      return (ty, a.properties, b.properties))
    (fun (ty,a,b) => do
      let p ← CreateProg.applyNative (ty,a,b) (fun (ty,a,b) => fold_srem ty a b)
      CreateProg.operation (.llvm .mlir__constant) #[] #[ty] p)
    (fun r => r)

theorem pattern_srem_valid : Pattern.Valid pattern_srem := by
  simp only [pattern_srem]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hdefined
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (srem_iff w rp _ _ rv).mp ri
  simp only [fold_srem, TypeAttr.of_val, Attribute.of, ha, hb]
  dsimp only [pure, Pure.pure]
  exists (.int w (.val (let x := BitVec.ofInt w a.value; let y := BitVec.ofInt w b.value; x.srem y)))
  constructor
  · exact (constant_iff _ _ _ rfl _).mpr (by simp only [BitVec.ofInt_toInt])
  · simp [LLVM.Int.srem, Id.run, pure, RuntimeValue.isRefinedBy, isRefinedBy]
    all_goals grind

/-- The upstream constant folder returns poison for a constant overshift. -/
def pattern_shl_poison : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .shl) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => !constantDefined_shl ty a b)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_shl_poison_valid : Pattern.Valid pattern_shl_poison := by
  simp only [pattern_shl_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hg
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (shl_iff w rp _ _ rv).mp ri
  have hn : w ≤ (BitVec.ofInt w b.value).toNat := by
    simpa [constantDefined_shl, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, ha, hb] using hg
  have hp : BitVec.ofNat w w ≤ BitVec.ofInt w b.value := by
    rw [BitVec.le_def]
    have hm := Nat.mod_le w (2^w)
    simp only [BitVec.toNat_ofNat]
    omega
  exists (.int w .poison)
  constructor
  · exact (poison_iff _ _ _).mpr rfl
  · simp [LLVM.Int.shl, Id.run, pure, hp, RuntimeValue.isRefinedBy, isRefinedBy]

/-- The upstream constant folder returns poison for a constant overshift. -/
def pattern_lshr_poison : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .lshr) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => !constantDefined_lshr ty a b)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_lshr_poison_valid : Pattern.Valid pattern_lshr_poison := by
  simp only [pattern_lshr_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hg
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (lshr_iff w rp _ _ rv).mp ri
  have hn : w ≤ (BitVec.ofInt w b.value).toNat := by
    simpa [constantDefined_lshr, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, ha, hb] using hg
  have hp : BitVec.ofNat w w ≤ BitVec.ofInt w b.value := by
    rw [BitVec.le_def]
    have hm := Nat.mod_le w (2^w)
    simp only [BitVec.toNat_ofNat]
    omega
  exists (.int w .poison)
  constructor
  · exact (poison_iff _ _ _).mpr rfl
  · simp [LLVM.Int.lshr, Id.run, pure, hp, RuntimeValue.isRefinedBy, isRefinedBy]

/-- The upstream constant folder returns poison for a constant overshift. -/
def pattern_ashr_poison : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .ashr) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => !constantDefined_ashr ty a b)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_ashr_poison_valid : Pattern.Valid pattern_ashr_poison := by
  simp only [pattern_ashr_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hg
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain rfl := (ashr_iff w rp _ _ rv).mp ri
  have hn : w ≤ (BitVec.ofInt w b.value).toNat := by
    simpa [constantDefined_ashr, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, ha, hb] using hg
  have hp : BitVec.ofNat w w ≤ BitVec.ofInt w b.value := by
    rw [BitVec.le_def]
    have hm := Nat.mod_le w (2^w)
    simp only [BitVec.toNat_ofNat]
    omega
  exists (.int w .poison)
  constructor
  · exact (poison_iff _ _ _).mpr rfl
  · simp [LLVM.Int.ashr, Id.run, pure, hp, RuntimeValue.isRefinedBy, isRefinedBy]

/-- The upstream constant folder returns poison for a constant undefined division/remainder. -/
def pattern_udiv_poison : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .udiv) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => !constantDefined_udiv ty a b)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_udiv_poison_valid : Pattern.Valid pattern_udiv_poison := by
  simp only [pattern_udiv_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hg
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (udiv_iff w rp _ _ rv).mp ri
  have hub : LLVM.Int.isUnsignedDivisionUB (.val (BitVec.ofInt w b.value)) = true := by
    simpa [constantDefined_udiv, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, ha, hb] using hg
  simp [hu] at hub

/-- The upstream constant folder returns poison for a constant undefined division/remainder. -/
def pattern_sdiv_poison : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .sdiv) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => !constantDefined_sdiv ty a b)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_sdiv_poison_valid : Pattern.Valid pattern_sdiv_poison := by
  simp only [pattern_sdiv_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hg
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (sdiv_iff w rp _ _ rv).mp ri
  have hub : LLVM.Int.isSignedDivisionUB (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) = true := by
    simpa [constantDefined_sdiv, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, ha, hb] using hg
  simp [hu] at hub

/-- The upstream constant folder returns poison for a constant undefined division/remainder. -/
def pattern_urem_poison : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .urem) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => !constantDefined_urem ty a b)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_urem_poison_valid : Pattern.Valid pattern_urem_poison := by
  simp only [pattern_urem_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hg
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (urem_iff w rp _ _ rv).mp ri
  have hub : LLVM.Int.isUnsignedDivisionUB (.val (BitVec.ofInt w b.value)) = true := by
    simpa [constantDefined_urem, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, ha, hb] using hg
  simp [hu] at hub

/-- The upstream constant folder returns poison for a constant undefined division/remainder. -/
def pattern_srem_poison : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let b ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty]
      let _ ← MatchProg.root (.llvm .srem) #[a.res[0]!, b.res[0]!] #[ty]
      MatchProg.matchNative (ty,a.properties,b.properties)
        (fun (ty,a,b) => !constantDefined_srem ty a b)
      return ty)
    (fun ty => do
      let p ← CreateProg.property (.llvm .mlir__poison) default
      CreateProg.operation (.llvm .mlir__poison) #[] #[ty] p)
    (fun r => r)

theorem pattern_srem_poison_valid : Pattern.Valid pattern_srem_poison := by
  simp only [pattern_srem_poison]
  provePuddleValid
  rintro ⟨w,s⟩ ap av ai bp bv bi rp rv ri hg
  obtain ⟨a,ha,rfl⟩ := constant_success _ ap av ai
  obtain ⟨b,hb,rfl⟩ := constant_success _ bp bv bi
  obtain ⟨hu,rfl⟩ := (srem_iff w rp _ _ rv).mp ri
  have hub : LLVM.Int.isSignedDivisionUB (.val (BitVec.ofInt w a.value)) (.val (BitVec.ofInt w b.value)) = true := by
    simpa [constantDefined_srem, TypeAttr.of_val, Attribute.of, -Attribute.integerType_eq_of, ha, hb] using hg
  simp [hu] at hub
end Veir.InstSimplify.IS0582
