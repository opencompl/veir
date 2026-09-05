import Veir.PatternRewriter.Puddle
import Veir.Dialects.LLVM.Properties
import Veir.PatternRewriter.Puddle.Validity

import Veir.GlobalOpInfo
import Veir.Dialects.LLVM.OpInfo
import Veir.Data.LLVM.Int.Lemmas
import Veir.Interpreter.Basic
import Veir.IR.Attribute
import Veir.Data.LLVM.Int.Basic
import Veir.Data.Refinement

import Veir.PatternRewriter.Puddle.Definitions
import Veir.PatternRewriter.Puddle.Builders

namespace Veir.InstCombinePuddle

open Puddle

public section

/-!
# InstCombine Puddle patterns

Puddle reimplementations of the peephole rewrites in `Veir.Passes.InstCombine`.

Puddle creation declarations contain concrete properties, rather than functions of values matched
at runtime. Consequently, the two patterns which create an integer zero are indexed by the integer
type they match. The family over all `IntegerType`s is the direct Puddle counterpart of the
type-polymorphic imperative rewrite.
-/

private theorem conformsInteger {type : IntegerType} {value : RuntimeValue}
    (h : value.Conforms (type : TypeAttr)) :
    ∃ x, value = .int type.bitwidth x := RuntimeValue.Conforms.integerType.mp h

private theorem forall_memoryState (p : Prop) : (∀ _ : MemoryState, p) ↔ p :=
  ⟨fun h => h .empty, fun h _ => h⟩

local macro "simpLLVM" : tactic =>
  `(tactic| (
    simp [TypeAttr.of, Coe.coe, InterpretsTo, interpretOp', Llvm.interpretOp', decodeLLVMIntegerConstant, bind, pure,
      RuntimeValue.isRefinedBy] at *
    try simp [forall_memoryState, and_assoc, and_left_comm, and_comm,
      RuntimeValue.ArrayConforms, RuntimeValue.conforms_integerType_iff]))

/-- The integer encoded by an LLVM constant attribute before resizing to the result type.
LLVM zero-extends i1 attributes and sign-extends all other integer attributes. -/
private def constantValue (value : IntegerAttr) : Int :=
  if value.type.bitwidth = 1 then (BitVec.ofInt 1 value.value).toNat
  else (BitVec.ofInt value.type.bitwidth value.value).toInt

private theorem matchedConstant {type : IntegerType} {properties : LLVMConstantProperties}
    {constant : Int} {result : RuntimeValue}
    (hmatch : (match properties.value with
      | .integer value => constantValue value == constant
      | _ => false) = true)
    (hop : InterpretsTo (.llvm .mlir__constant) properties #[type] #[] #[result]) :
    result = .int type.bitwidth (Data.LLVM.Int.constant type.bitwidth constant) := by
  obtain ⟨property⟩ := properties
  cases property <;> simp only at hmatch
  all_goals try contradiction
  rename_i attr
  simp only [beq_iff_eq] at hmatch
  have hop := hop.2 MemoryState.empty
  simp [interpretOp', Llvm.interpretOp', pure] at hop
  change RuntimeValue.int type.bitwidth
    (Data.LLVM.Int.constant type.bitwidth (constantValue attr)) = result at hop
  simpa only [hmatch] using hop.symm

/-- Match an LLVM integer constant by its decoded value, including attribute-width truncation. -/
private def matchConstant (returnType : Handle OpCode .type) (constant : Int) :
    MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.llvm .mlir__constant) #[] #[returnType]
    (fun properties =>
      match properties.value with
      | .integer value => constantValue value == constant
      | _ => false)
  return op.res[0]!

/-- Create an LLVM integer constant of a given value. -/
private def createConstant (returnType : Handle OpCode .type) (integerType : IntegerType)
    (value : Int) : CreateProg.Builder CreatedOpHandle := do
  let properties ← CreateProg.property (.llvm .mlir__constant)
    (LLVMConstantProperties.mk (.integer (IntegerAttr.mk value integerType)))
  CreateProg.operation (.llvm .mlir__constant) #[] #[returnType] properties

private theorem mulTwo_eq_addSelf {w : Nat} (hw : 2 < w) (x : Data.LLVM.Int w)
    (nsw nuw : Bool) :
    x.mul (Data.LLVM.Int.constant w 2) nsw nuw = x.add x nsw nuw := by
  cases x with
  | poison => rfl
  | val x =>
    have hpow : 8 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (i := 3) (by decide) hw
    have ht : (BitVec.ofInt w 2).toInt = 2 := by
      rw [BitVec.toInt_ofInt]
      apply Int.bmod_eq_of_le <;> omega
    have hn : (BitVec.ofInt w 2).toNat = 2 := by
      simp [BitVec.ofInt_ofNat, Nat.mod_eq_of_lt (by omega : 2 < 2 ^ w)]
    have hs : x.smulOverflow (BitVec.ofInt w 2) = x.saddOverflow x := by
      simp only [BitVec.smulOverflow, BitVec.saddOverflow, ht]
      have h : x.toInt * 2 = x.toInt + x.toInt := by omega
      rw [h]
    have hu : x.umulOverflow (BitVec.ofInt w 2) = x.uaddOverflow x := by
      simp only [BitVec.umulOverflow, BitVec.uaddOverflow, hn, Nat.mul_two]
    simp only [Data.LLVM.Int.mul, Data.LLVM.Int.add, Data.LLVM.Int.constant, Id.run]
    rw [hs, hu]
    simp [BitVec.ofInt_ofNat, BitVec.mul_two]

/-- Rewrites `x * 2` to `x + x` at widths of at least three bits, preserving overflow flags. -/
def mulITwoToAddi (properties : NswNuwProperties) : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType) (fun type => 2 < type.bitwidth)
      let x ← MatchProg.value returnType
      let two ← matchConstant returnType 2
      let _ ← MatchProg.root (.llvm .mul) #[x, two] #[returnType]
        (fun actual => actual == properties)
      return (returnType, x))
    (fun (returnType, x) => do
      let properties ← CreateProg.property (.llvm .add) properties
      CreateProg.operation (.llvm .add) #[x, x] #[returnType] properties)
    (fun add => add)

theorem mulITwoToAddi_valid (properties : NswNuwProperties) :
    Pattern.Valid (mulITwoToAddi properties) := by
  simp only [mulITwoToAddi, matchConstant]
  provePuddleValid
  rintro _ type rfl hwidth value hv constantProperties constant hc hconstant actualProperties result hp hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  change NswNuwProperties at actualProperties
  change (actualProperties == properties) = true at hp
  simp only [beq_iff_eq] at hp
  subst actualProperties
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp [mulTwo_eq_addSelf hwidth]

/-- Rewrites `x * 0` to the matched zero. -/
def mulIZeroToCst : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let zero ← matchConstant returnType 0
      let _ ← MatchProg.root (.llvm .mul) #[x, zero] #[returnType]
      return zero)
    pure
    (fun zero => zero)

theorem mulIZeroToCst_valid : Pattern.Valid mulIZeroToCst := by
  simp only [mulIZeroToCst, matchConstant]
  provePuddleValid
  intro type value hv constantProperties constant hc hconstant properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    simp only [Data.LLVM.Int.mul, Data.LLVM.Int.constant, Id.run, pure]
    split
    · trivial
    · split <;> simp [isRefinedBy]

/-- Rewrites `x + 0` to `x`. -/
def addiZeroToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let zero ← matchConstant returnType 0
      let _ ← MatchProg.root (.llvm .add) #[x, zero] #[returnType]
      return x)
    pure
    (fun x => x)

theorem addiZeroToX_valid : Pattern.Valid addiZeroToX := by
  simp only [addiZeroToX, matchConstant]
  provePuddleValid
  intro type value hv constantProperties constant hc hconstant properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simp [Data.LLVM.Int.add_zero]

/-- Rewrites `x * 1` to `x`. -/
def mulIOneToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let one ← matchConstant returnType 1
      let _ ← MatchProg.root (.llvm .mul) #[x, one] #[returnType]
      return x)
    pure
    (fun x => x)

theorem mulIOneToX_valid : Pattern.Valid mulIOneToX := by
  simp only [mulIOneToX, matchConstant]
  provePuddleValid
  intro type value hv constantProperties constant hc hconstant properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simpa using Data.LLVM.Int.mul_one_refines x properties.nsw properties.nuw

/-- Rewrites `x - 0` to `x`. -/
def subiZeroToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let zero ← matchConstant returnType 0
      let _ ← MatchProg.root (.llvm .sub) #[x, zero] #[returnType]
      return x)
    pure
    (fun x => x)

theorem subiZeroToX_valid : Pattern.Valid subiZeroToX := by
  simp only [subiZeroToX, matchConstant]
  provePuddleValid
  intro type value hv constantProperties constant hc hconstant properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  simp [Data.LLVM.Int.sub_zero]

/-- Rewrites `x - x` to `0` for the given integer type. -/
def subiSelfToZero (integerType : IntegerType) : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType) (fun actual => actual == integerType)
      let x ← MatchProg.value returnType
      let _ ← MatchProg.root (.llvm .sub) #[x, x] #[returnType]
      return returnType)
    (fun returnType => createConstant returnType integerType 0)
    (fun zero => zero)

theorem subiSelfToZero_valid (integerType : IntegerType) :
    Pattern.Valid (subiSelfToZero integerType) := by
  simp only [subiSelfToZero, createConstant]
  provePuddleValid
  rintro _ type rfl htype value hv properties result hop
  change NswNuwProperties at properties
  subst integerType
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x <;> simp only [Data.LLVM.Int.sub, Id.run, pure]
  all_goals first
    | trivial
    | (split
       · trivial
       · split <;> simp [isRefinedBy])

/-- Rewrites `x & x` to `x`. -/
def andiSelfToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let _ ← MatchProg.root (.llvm .and) #[x, x] #[returnType]
      return x)
    pure
    (fun x => x)

theorem andiSelfToX_valid : Pattern.Valid andiSelfToX := by
  simp only [andiSelfToX]
  provePuddleValid
  intro type value hv properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  cases x <;> simp [Data.LLVM.Int.and, Id.run, isRefinedBy]

/-- Rewrites `x & 0` to the matched zero. -/
def andiZeroToZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let zero ← matchConstant returnType 0
      let _ ← MatchProg.root (.llvm .and) #[x, zero] #[returnType]
      return zero)
    pure
    (fun zero => zero)

theorem andiZeroToZero_valid : Pattern.Valid andiZeroToZero := by
  simp only [andiZeroToZero, matchConstant]
  provePuddleValid
  intro type value hv constantProperties constant hc hconstant properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x <;> simp [Data.LLVM.Int.and, Data.LLVM.Int.constant, Id.run, isRefinedBy]

/-- Rewrites `x | 0` to `x`. -/
def oriZeroToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let zero ← matchConstant returnType 0
      let _ ← MatchProg.root (.llvm .or) #[x, zero] #[returnType]
      return x)
    pure
    (fun x => x)

theorem oriZeroToX_valid : Pattern.Valid oriZeroToX := by
  simp only [oriZeroToX, matchConstant]
  provePuddleValid
  intro type value hv constantProperties constant hc hconstant properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x <;> simp [Data.LLVM.Int.or, Data.LLVM.Int.constant, Id.run, isRefinedBy]

/-- Rewrites `x | x` to `x`. -/
def oriSelfToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let _ ← MatchProg.root (.llvm .or) #[x, x] #[returnType]
      return x)
    pure
    (fun x => x)

theorem oriSelfToX_valid : Pattern.Valid oriSelfToX := by
  simp only [oriSelfToX]
  provePuddleValid
  intro type value hv properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x with
  | poison => trivial
  | val x =>
    simp only [Data.LLVM.Int.or, Id.run, pure]
    split <;> simp [isRefinedBy]

/-- Rewrites `x ^ 0` to `x`. -/
def xoriZeroToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let zero ← matchConstant returnType 0
      let _ ← MatchProg.root (.llvm .xor) #[x, zero] #[returnType]
      return x)
    pure
    (fun x => x)

theorem xoriZeroToX_valid : Pattern.Valid xoriZeroToX := by
  simp only [xoriZeroToX, matchConstant]
  provePuddleValid
  intro type value hv constantProperties constant hc hconstant properties result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc hconstant
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x <;> simp [Data.LLVM.Int.xor, Data.LLVM.Int.constant, Id.run, isRefinedBy]

/-- Rewrites `x ^ x` to `0` for the given integer type. -/
def xoriSelfToZero (integerType : IntegerType) : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType) (fun actual => actual == integerType)
      let x ← MatchProg.value returnType
      let _ ← MatchProg.root (.llvm .xor) #[x, x] #[returnType]
      return returnType)
    (fun returnType => createConstant returnType integerType 0)
    (fun zero => zero)

theorem xoriSelfToZero_valid (integerType : IntegerType) :
    Pattern.Valid (xoriSelfToZero integerType) := by
  simp only [xoriSelfToZero, createConstant]
  provePuddleValid
  rintro _ type rfl htype value hv properties result hop
  subst integerType
  obtain ⟨x, rfl⟩ := conformsInteger hv
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases x <;> simp [Data.LLVM.Int.xor, Id.run, isRefinedBy]

/-- Match `x ^ -1`, the canonical LLVM representation of `~x`. -/
private def matchNot (returnType : Handle OpCode .type) (x : Handle OpCode .value) :
    MatchProg.Builder (Handle OpCode .value) := do
  let minusOne ← matchConstant returnType (-1)
  let not ← MatchProg.operation (.llvm .xor) #[x, minusOne] #[returnType]
  return not.res[0]!

/-- Rewrites `~~x` to `x`. -/
def notNotToX : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let innerNot ← matchNot returnType x
      let minusOne ← matchConstant returnType (-1)
      let _ ← MatchProg.root (.llvm .xor) #[innerNot, minusOne] #[returnType]
      return x)
    pure
    (fun x => x)

theorem notNotToX_valid : Pattern.Valid notNotToX := by
  simp only [notNotToX, matchNot, matchConstant]
  provePuddleValid
  intro type value hv cp₁ c₁ hc₁ hconst₁ xp₁ inner hinner cp₂ c₂ hc₂ hconst₂ xp₂ result hop
  obtain ⟨x, rfl⟩ := conformsInteger hv
  obtain rfl := matchedConstant hc₁ hconst₁
  obtain rfl := matchedConstant hc₂ hconst₂
  simpLLVM
  have hinner := hinner.2 MemoryState.empty
  subst inner
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  cases x <;> simp [Data.LLVM.Int.xor, Data.LLVM.Int.constant, Id.run, isRefinedBy, BitVec.xor_assoc]

/-- Rewrites `~(~a & ~b)` to `a | b` (De Morgan). -/
def deMorganAndToOr : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value returnType
      let b ← MatchProg.value returnType
      let notA ← matchNot returnType a
      let notB ← matchNot returnType b
      let and ← MatchProg.operation (.llvm .and) #[notA, notB] #[returnType]
      let minusOne ← matchConstant returnType (-1)
      let _ ← MatchProg.root (.llvm .xor) #[and.res[0]!, minusOne] #[returnType]
      return (returnType, a, b))
    (fun (returnType, a, b) => do
      let properties ← CreateProg.property (.llvm .or)
        ({ disjoint := false } : DisjointProperties)
      CreateProg.operation (.llvm .or) #[a, b] #[returnType] properties)
    (fun or => or)

theorem deMorganAndToOr_valid : Pattern.Valid deMorganAndToOr := by
  simp only [deMorganAndToOr, matchNot, matchConstant]
  provePuddleValid
  intro type a ha b hb cp₁ c₁ hc₁ hconst₁ xp₁ notA hnotA cp₂ c₂ hc₂ hconst₂
    xp₂ notB hnotB bp combined hcombined cp₃ c₃ hc₃ hconst₃ xp₃ result hop
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  obtain rfl := matchedConstant hc₁ hconst₁
  obtain rfl := matchedConstant hc₂ hconst₂
  obtain rfl := matchedConstant hc₃ hconst₃
  simpLLVM
  have hnotA := hnotA.2 MemoryState.empty
  have hnotB := hnotB.2 MemoryState.empty
  subst notA notB
  simpLLVM
  have hcombined := hcombined.2 MemoryState.empty
  subst combined
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases a <;> cases b <;>
    simp [Data.LLVM.Int.xor, Data.LLVM.Int.and, Data.LLVM.Int.or,
      Data.LLVM.Int.constant, Id.run, isRefinedBy, BitVec.ofInt_neg,
      BitVec.neg_one_eq_allOnes, BitVec.not_and]

/-- Rewrites `~(~a | ~b)` to `a & b` (De Morgan). -/
def deMorganOrToAnd : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let a ← MatchProg.value returnType
      let b ← MatchProg.value returnType
      let notA ← matchNot returnType a
      let notB ← matchNot returnType b
      let or ← MatchProg.operation (.llvm .or) #[notA, notB] #[returnType]
      let minusOne ← matchConstant returnType (-1)
      let _ ← MatchProg.root (.llvm .xor) #[or.res[0]!, minusOne] #[returnType]
      return (returnType, a, b))
    (fun (returnType, a, b) => do
      let properties ← CreateProg.property (.llvm .and) ()
      CreateProg.operation (.llvm .and) #[a, b] #[returnType] properties)
    (fun and => and)

theorem deMorganOrToAnd_valid : Pattern.Valid deMorganOrToAnd := by
  simp only [deMorganOrToAnd, matchNot, matchConstant]
  provePuddleValid
  intro type a ha b hb cp₁ c₁ hc₁ hconst₁ xp₁ notA hnotA cp₂ c₂ hc₂ hconst₂
    xp₂ notB hnotB bp combined hcombined cp₃ c₃ hc₃ hconst₃ xp₃ result hop
  change DisjointProperties at bp
  obtain ⟨a, rfl⟩ := conformsInteger ha
  obtain ⟨b, rfl⟩ := conformsInteger hb
  obtain rfl := matchedConstant hc₁ hconst₁
  obtain rfl := matchedConstant hc₂ hconst₂
  obtain rfl := matchedConstant hc₃ hconst₃
  simpLLVM
  have hnotA := hnotA.2 MemoryState.empty
  have hnotB := hnotB.2 MemoryState.empty
  subst notA notB
  simpLLVM
  have hcombined := hcombined.2 MemoryState.empty
  subst combined
  simpLLVM
  rw [← hop.2 MemoryState.empty]
  simp only [Data.LLVM.Int.cast_self, exists_const]
  cases a <;> cases b <;>
    simp [Data.LLVM.Int.xor, Data.LLVM.Int.and, Data.LLVM.Int.or,
      Data.LLVM.Int.constant, Id.run, pure, isRefinedBy, BitVec.ofInt_neg,
      BitVec.neg_one_eq_allOnes]
  rename_i a b
  by_cases hd : bp.disjoint = true ∧ ~~~a &&& ~~~b ≠ 0#type.bitwidth <;>
    simp [hd, BitVec.not_or]

end

end Veir.InstCombinePuddle
