import Veir.Passes.ArithCanonicalize.ExtendedSupport
import Veir.Passes.ArithCanonicalize.SelectSupport
import Veir.Passes.ArithCanonicalize.DivisionSupport

/-! Scalar integer instances of CommonFolders binary poison propagation. -/
set_option linter.unusedSimpArgs false
namespace Veir.ArithCanonicalize.G004

open Veir Veir.Puddle Veir.Data Veir.ArithPuddle
open Veir.ArithCanonicalize.SelectSupport
open Veir.ArithCanonicalize.ExtendedSupport

def addiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .addi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem addiValid (poisonOnRight : Bool) : Pattern.Valid (addiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [addiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (addi_iff w p .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.add, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (addi_iff w p x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.add, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def subiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .subi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem subiValid (poisonOnRight : Bool) : Pattern.Valid (subiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [subiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (subi_iff w p .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.sub, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (subi_iff w p x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.sub, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def muliPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .muli)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem muliValid (poisonOnRight : Bool) : Pattern.Valid (muliPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [muliPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (muli_iff w p .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.mul, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (muli_iff w p x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.mul, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def andiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .andi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem andiValid (poisonOnRight : Bool) : Pattern.Valid (andiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [andiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (andi_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.and, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (andi_iff w x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.and, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def oriPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .ori)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem oriValid (poisonOnRight : Bool) : Pattern.Valid (oriPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [oriPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (ori_iff w p .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (ori_iff w p x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.or, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def xoriPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .xori)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem xoriValid (poisonOnRight : Bool) : Pattern.Valid (xoriPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [xoriPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (xori_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (xori_iff w x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.xor, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def maxsiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .maxsi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem maxsiValid (poisonOnRight : Bool) : Pattern.Valid (maxsiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [maxsiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (maxsi_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (maxsi_iff w x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.smax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def maxuiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .maxui)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem maxuiValid (poisonOnRight : Bool) : Pattern.Valid (maxuiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [maxuiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (maxui_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (maxui_iff w x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.umax, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def minsiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .minsi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem minsiValid (poisonOnRight : Bool) : Pattern.Valid (minsiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [minsiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (minsi_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (minsi_iff w x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.smin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def minuiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .minui)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem minuiValid (poisonOnRight : Bool) : Pattern.Valid (minuiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [minuiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain rfl := (minui_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain rfl := (minui_iff w x .poison r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.umin, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def divuiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .divui)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem divuiValid (poisonOnRight : Bool) : Pattern.Valid (divuiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [divuiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨_, rfl⟩ := (divui_iff w p .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.udiv, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨hUB, rfl⟩ := (divui_iff w p x .poison r).mp hr
    simp [LLVM.Int.isUnsignedDivisionUB] at hUB

def divsiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .divsi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem divsiValid (poisonOnRight : Bool) : Pattern.Valid (divsiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [divsiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨_, rfl⟩ := (divsi_iff w p .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.sdiv, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨hisSignedDivisionUB, rfl⟩ := (divsi_iff w p x .poison r).mp hr
    simp [LLVM.Int.isSignedDivisionUB] at hisSignedDivisionUB

def remuiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .remui)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem remuiValid (poisonOnRight : Bool) : Pattern.Valid (remuiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [remuiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨_, rfl⟩ := (remui_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.urem, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨hisUnsignedDivisionUB, rfl⟩ := (remui_iff w x .poison r).mp hr
    simp [LLVM.Int.isUnsignedDivisionUB] at hisUnsignedDivisionUB

def remsiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .remsi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem remsiValid (poisonOnRight : Bool) : Pattern.Valid (remsiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [remsiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨_, rfl⟩ := (remsi_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [LLVM.Int.srem, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨hisSignedDivisionUB, rfl⟩ := (remsi_iff w x .poison r).mp hr
    simp [LLVM.Int.isSignedDivisionUB] at hisSignedDivisionUB

def ceildivuiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .ceildivui)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem ceildivuiValid (poisonOnRight : Bool) : Pattern.Valid (ceildivuiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [ceildivuiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨_, rfl⟩ := (Veir.ArithCanonicalize.ceildivui_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [uceilResult, LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.sub, LLVM.Int.sdiv, LLVM.Int.udiv, LLVM.Int.mul, LLVM.Int.and, LLVM.Int.add, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨hisUnsignedDivisionUB, rfl⟩ := (Veir.ArithCanonicalize.ceildivui_iff w x .poison r).mp hr
    simp [LLVM.Int.isUnsignedDivisionUB] at hisUnsignedDivisionUB

def ceildivsiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .ceildivsi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem ceildivsiValid (poisonOnRight : Bool) : Pattern.Valid (ceildivsiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [ceildivsiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨_, rfl⟩ := (Veir.ArithCanonicalize.ceildivsi_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [sceilResult, LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.sub, LLVM.Int.sdiv, LLVM.Int.udiv, LLVM.Int.mul, LLVM.Int.and, LLVM.Int.add, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨hisSignedDivisionUB, rfl⟩ := (Veir.ArithCanonicalize.ceildivsi_iff w x .poison r).mp hr
    simp [LLVM.Int.isSignedDivisionUB] at hisSignedDivisionUB

def floordivsiPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .floordivsi)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x]) #[ty]
      return (ty, poison.properties))
    (fun (ty, props) => CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props)
    (fun result => result)

theorem floordivsiValid (poisonOnRight : Bool) : Pattern.Valid (floordivsiPattern poisonOnRight) := by
  cases poisonOnRight <;> simp only [floordivsiPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r hr
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨_, rfl⟩ := (Veir.ArithCanonicalize.floordivsi_iff w .poison x r).mp hr
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl, ?_⟩
    cases x <;> simp [sfloorResult, LLVM.Int.select, LLVM.Int.icmp, LLVM.Int.sub, LLVM.Int.sdiv, LLVM.Int.udiv, LLVM.Int.mul, LLVM.Int.and, LLVM.Int.add, RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨hisSignedDivisionUB, rfl⟩ := (Veir.ArithCanonicalize.floordivsi_iff w x .poison r).mp hr
    simp [LLVM.Int.isSignedDivisionUB] at hisSignedDivisionUB

def addui_extendedPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let carryTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .addui_extended)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x])
        #[ty, carryTy]
      return (ty, carryTy, poison.properties))
    (fun (ty, carryTy, props) => do
      let low ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props
      let high ← CreateProg.operation (.llvm .mlir__poison) #[] #[carryTy] props
      return (low.res[0]!, high.res[0]!))
    (fun (low, high) => #[low, high])

theorem addui_extendedValid (poisonOnRight : Bool) :
    Pattern.Valid (addui_extendedPattern poisonOnRight) := by
  cases poisonOnRight <;>
    simp only [addui_extendedPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ carryTy ⟨cw, t⟩ hTy hBool ⟨⟩ pv hp x hx p r0 r1 hi
    cases hTy
    cases hBool
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨rfl, rfl⟩ := (addui_extended_iff w .poison x r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int 1 .poison, (poison_iff 1 _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.add, LLVM.Int.uaddOverflowFlag,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨rfl, rfl⟩ := (addui_extended_iff w x .poison r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int 1 .poison, (poison_iff 1 _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.add, LLVM.Int.uaddOverflowFlag,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def subui_extendedPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let carryTy ← MatchProg.type (Attr := IntegerType)
        (fun t => t == IntegerType.signless 1)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .subui_extended)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x])
        #[ty, carryTy]
      return (ty, carryTy, poison.properties))
    (fun (ty, carryTy, props) => do
      let low ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props
      let high ← CreateProg.operation (.llvm .mlir__poison) #[] #[carryTy] props
      return (low.res[0]!, high.res[0]!))
    (fun (low, high) => #[low, high])

theorem subui_extendedValid (poisonOnRight : Bool) :
    Pattern.Valid (subui_extendedPattern poisonOnRight) := by
  cases poisonOnRight <;>
    simp only [subui_extendedPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ carryTy ⟨cw, t⟩ hTy hBool ⟨⟩ pv hp x hx p r0 r1 hi
    cases hTy
    cases hBool
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨rfl, rfl⟩ := (subui_extended_iff w .poison x r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int 1 .poison, (poison_iff 1 _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.sub, LLVM.Int.usubOverflowFlag,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨rfl, rfl⟩ := (subui_extended_iff w x .poison r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int 1 .poison, (poison_iff 1 _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.sub, LLVM.Int.usubOverflowFlag,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def mulsi_extendedPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .mulsi_extended)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x])
        #[ty, ty]
      return (ty, poison.properties))
    (fun (ty, props) => do
      let low ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props
      let high ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props
      return (low.res[0]!, high.res[0]!))
    (fun (low, high) => #[low, high])

theorem mulsi_extendedValid (poisonOnRight : Bool) :
    Pattern.Valid (mulsi_extendedPattern poisonOnRight) := by
  cases poisonOnRight <;>
    simp only [mulsi_extendedPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r0 r1 hi
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨rfl, rfl⟩ := (mulsi_extended_iff w .poison x r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int w .poison, (poison_iff w _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.mul, LLVM.Int.smulHigh,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨rfl, rfl⟩ := (mulsi_extended_iff w x .poison r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int w .poison, (poison_iff w _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.mul, LLVM.Int.smulHigh,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

def mului_extendedPattern (poisonOnRight : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let poison ← MatchProg.operation (.llvm .mlir__poison) #[] #[ty]
      let x ← MatchProg.value ty
      let _ ← MatchProg.root (.arith .mului_extended)
        (if poisonOnRight then #[x, poison.res[0]!] else #[poison.res[0]!, x])
        #[ty, ty]
      return (ty, poison.properties))
    (fun (ty, props) => do
      let low ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props
      let high ← CreateProg.operation (.llvm .mlir__poison) #[] #[ty] props
      return (low.res[0]!, high.res[0]!))
    (fun (low, high) => #[low, high])

theorem mului_extendedValid (poisonOnRight : Bool) :
    Pattern.Valid (mului_extendedPattern poisonOnRight) := by
  cases poisonOnRight <;>
    simp only [mului_extendedPattern, Bool.false_eq_true, ↓reduceIte] <;>
    provePuddleValid
  all_goals
    rintro ⟨w, s⟩ ⟨⟩ pv hp x hx p r0 r1 hi
    obtain rfl := (poison_iff w pv).mp hp
    obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hx
  · obtain ⟨rfl, rfl⟩ := (mului_extended_iff w .poison x r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int w .poison, (poison_iff w _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.mul, LLVM.Int.umulHigh,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]
  · obtain ⟨rfl, rfl⟩ := (mului_extended_iff w x .poison r0 r1).mp hi
    refine ⟨.int w .poison, (poison_iff w _).mpr rfl,
      .int w .poison, (poison_iff w _).mpr rfl, ?_, ?_⟩
    all_goals cases x <;>
      simp [LLVM.Int.mul, LLVM.Int.umulHigh,
        RuntimeValue.isRefinedBy, isRefinedBy, Id.run]

end Veir.ArithCanonicalize.G004
