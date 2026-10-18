module

public import Veir.Passes.InstCombineLLVM.SelectSemantics
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.SelectLogicalXor

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM

public def pattern (andSelect orSelect notLeft outerSwapped orSwapped : Bool) :
    Pattern OpCode := Pattern.Builder
  (do
    let ty ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth = 1)
    let a ← MatchProg.value ty
    let b ← MatchProg.value ty
    let zero ← matchSelectConstant ty 0
    let one ← matchSelectConstant ty 1
    let innerAnd ← (if andSelect then
      do
        let op ← MatchProg.operation (.llvm .select) #[a, b, zero] #[ty] (fun _ => true)
        return op.res[0]!
    else
      do
        let op ← MatchProg.operation (.llvm .and) #[a, b] #[ty] (fun _ => true)
        return op.res[0]!)
    let notInner ← MatchProg.operation (.llvm .xor)
      (if notLeft then #[one, innerAnd] else #[innerAnd, one])
      #[ty] (fun _ => true)
    let innerOr ← (if orSelect then
      do
        let op ← MatchProg.operation (.llvm .select)
          (if orSwapped then #[b, one, a] else #[a, one, b]) #[ty] (fun _ => true)
        return op.res[0]!
    else
      do
        let op ← MatchProg.operation (.llvm .or)
          (if orSwapped then #[b, a] else #[a, b]) #[ty] (fun _ => true)
        return op.res[0]!)
    let root ← MatchProg.root (.llvm .select)
      (if outerSwapped then #[innerOr, notInner.res[0]!, zero]
       else #[notInner.res[0]!, innerOr, zero]) #[ty] (fun _ => true)
    return (ty, a, b))
  (fun (ty, a, b) => do
    let properties ← CreateProg.property (.llvm .xor) ()
    CreateProg.operation (.llvm .xor) #[a, b] #[ty] properties)
  (fun result => result.res[0]!)

set_option maxHeartbeats 4000000 in
public theorem pattern_valid (andSelect orSelect notLeft outerSwapped orSwapped : Bool) :
    Pattern.Valid (pattern andSelect orSelect notLeft outerSwapped orSwapped) := by
  cases andSelect <;> cases orSelect <;> cases notLeft <;>
    cases outerSwapped <;> cases orSwapped <;>
    simp only [pattern, Bool.false_eq_true, Bool.true_eq, ite_false, ite_true,
      matchSelectConstant] <;> unfoldPuddleBuilder
  all_goals
    proveScalarPuddleStructure
    simpPuddleSemantics
    rintro type ⟨w, signedness⟩ hType hWidth
    subst type
    change w = 1 at hWidth
    subst w
    rintro a hA b hB
    obtain ⟨a, rfl⟩ := RuntimeValue.Conforms.integerType.mp hA
    obtain ⟨b, rfl⟩ := RuntimeValue.Conforms.integerType.mp hB
    rintro zeroProperty zero hZero hZeroInterp
    let zeroProperty' : LLVMConstantProperties := asLLVMConstantProperties zeroProperty
    change (match zeroProperty'.value with
      | .integer attr => decide (attr.value = 0)
      | _ => false) = true at hZero
    change InterpretsTo (.llvm .mlir__constant) zeroProperty'
      #[IntegerType.mk 1 signedness] #[] #[zero] at hZeroInterp
    rcases zeroProperty' with ⟨zeroValue⟩
    cases zeroValue with
    | float _ | dense _ | string _ => simp at hZero
    | integer zeroAttr =>
      simp at hZero
      obtain rfl := (constant_iff _ zeroAttr _).mp hZeroInterp
      rintro oneProperty one hOne hOneInterp
      let oneProperty' : LLVMConstantProperties := asLLVMConstantProperties oneProperty
      change (match oneProperty'.value with
        | .integer attr => decide (attr.value = 1)
        | _ => false) = true at hOne
      change InterpretsTo (.llvm .mlir__constant) oneProperty'
        #[IntegerType.mk 1 signedness] #[] #[one] at hOneInterp
      rcases oneProperty' with ⟨oneValue⟩
      cases oneValue with
      | float _ | dense _ | string _ => simp at hOne
      | integer oneAttr =>
        simp at hOne
        obtain rfl := (constant_iff _ oneAttr _).mp hOneInterp
        rintro innerAndProperties innerAnd hInnerAnd
        first
        | obtain rfl := (and_iff _ _ _ _).mp hInnerAnd
        | obtain rfl := (select_iff _ _ _ _ _).mp hInnerAnd
        rintro ⟨⟩ notInner hNotInner
        obtain rfl := (xor_iff _ _ _ _).mp hNotInner
        rintro innerOrProperties innerOr hInnerOr
        first
        | obtain rfl := (or_iff _ innerOrProperties _ _ _).mp hInnerOr
        | obtain rfl := (select_iff _ _ _ _ _).mp hInnerOr
        rintro ⟨⟩ source hSource
        obtain rfl := (select_iff _ _ _ _ _).mp hSource
        try rintro ⟨⟩
        simp [IsTypeAttr.cast?_of]
        refine ⟨.int 1 (LLVM.Int.xor a b), (xor_iff _ _ _ _).mpr rfl, ?_⟩
        refine ⟨rfl, ?_⟩
        rw [hZero, hOne]
        simp only [LLVM.Int.cast_self]
        first
        | exact select_demorgan_xor false false false false false a b innerOrProperties.disjoint
        | exact select_demorgan_xor false false false false true a b innerOrProperties.disjoint
        | exact select_demorgan_xor false false false true false a b innerOrProperties.disjoint
        | exact select_demorgan_xor false false false true true a b innerOrProperties.disjoint
        | exact select_demorgan_xor false false true false false a b innerOrProperties.disjoint
        | exact select_demorgan_xor false false true false true a b innerOrProperties.disjoint
        | exact select_demorgan_xor false false true true false a b innerOrProperties.disjoint
        | exact select_demorgan_xor false false true true true a b innerOrProperties.disjoint
        | exact select_demorgan_xor false true false false false a b false
        | exact select_demorgan_xor false true false false true a b false
        | exact select_demorgan_xor false true false true false a b false
        | exact select_demorgan_xor false true false true true a b false
        | exact select_demorgan_xor false true true false false a b false
        | exact select_demorgan_xor false true true false true a b false
        | exact select_demorgan_xor false true true true false a b false
        | exact select_demorgan_xor false true true true true a b false
        | exact select_demorgan_xor true false false false false a b innerOrProperties.disjoint
        | exact select_demorgan_xor true false false false true a b innerOrProperties.disjoint
        | exact select_demorgan_xor true false false true false a b innerOrProperties.disjoint
        | exact select_demorgan_xor true false false true true a b innerOrProperties.disjoint
        | exact select_demorgan_xor true false true false false a b innerOrProperties.disjoint
        | exact select_demorgan_xor true false true false true a b innerOrProperties.disjoint
        | exact select_demorgan_xor true false true true false a b innerOrProperties.disjoint
        | exact select_demorgan_xor true false true true true a b innerOrProperties.disjoint
        | exact select_demorgan_xor true true false false false a b false
        | exact select_demorgan_xor true true false false true a b false
        | exact select_demorgan_xor true true false true false a b false
        | exact select_demorgan_xor true true false true true a b false
        | exact select_demorgan_xor true true true false false a b false
        | exact select_demorgan_xor true true true false true a b false
        | exact select_demorgan_xor true true true true false a b false
        | exact select_demorgan_xor true true true true true a b false

public def selectLogicalXor00000 : Pattern OpCode := pattern false false false false false
public theorem selectLogicalXor00000_valid : Pattern.Valid selectLogicalXor00000 :=
  pattern_valid false false false false false

public def selectLogicalXor00001 : Pattern OpCode := pattern false false false false true
public theorem selectLogicalXor00001_valid : Pattern.Valid selectLogicalXor00001 :=
  pattern_valid false false false false true

public def selectLogicalXor00010 : Pattern OpCode := pattern false false false true false
public theorem selectLogicalXor00010_valid : Pattern.Valid selectLogicalXor00010 :=
  pattern_valid false false false true false

public def selectLogicalXor00011 : Pattern OpCode := pattern false false false true true
public theorem selectLogicalXor00011_valid : Pattern.Valid selectLogicalXor00011 :=
  pattern_valid false false false true true

public def selectLogicalXor00100 : Pattern OpCode := pattern false false true false false
public theorem selectLogicalXor00100_valid : Pattern.Valid selectLogicalXor00100 :=
  pattern_valid false false true false false

public def selectLogicalXor00101 : Pattern OpCode := pattern false false true false true
public theorem selectLogicalXor00101_valid : Pattern.Valid selectLogicalXor00101 :=
  pattern_valid false false true false true

public def selectLogicalXor00110 : Pattern OpCode := pattern false false true true false
public theorem selectLogicalXor00110_valid : Pattern.Valid selectLogicalXor00110 :=
  pattern_valid false false true true false

public def selectLogicalXor00111 : Pattern OpCode := pattern false false true true true
public theorem selectLogicalXor00111_valid : Pattern.Valid selectLogicalXor00111 :=
  pattern_valid false false true true true

public def selectLogicalXor01000 : Pattern OpCode := pattern false true false false false
public theorem selectLogicalXor01000_valid : Pattern.Valid selectLogicalXor01000 :=
  pattern_valid false true false false false

public def selectLogicalXor01001 : Pattern OpCode := pattern false true false false true
public theorem selectLogicalXor01001_valid : Pattern.Valid selectLogicalXor01001 :=
  pattern_valid false true false false true

public def selectLogicalXor01010 : Pattern OpCode := pattern false true false true false
public theorem selectLogicalXor01010_valid : Pattern.Valid selectLogicalXor01010 :=
  pattern_valid false true false true false

public def selectLogicalXor01011 : Pattern OpCode := pattern false true false true true
public theorem selectLogicalXor01011_valid : Pattern.Valid selectLogicalXor01011 :=
  pattern_valid false true false true true

public def selectLogicalXor01100 : Pattern OpCode := pattern false true true false false
public theorem selectLogicalXor01100_valid : Pattern.Valid selectLogicalXor01100 :=
  pattern_valid false true true false false

public def selectLogicalXor01101 : Pattern OpCode := pattern false true true false true
public theorem selectLogicalXor01101_valid : Pattern.Valid selectLogicalXor01101 :=
  pattern_valid false true true false true

public def selectLogicalXor01110 : Pattern OpCode := pattern false true true true false
public theorem selectLogicalXor01110_valid : Pattern.Valid selectLogicalXor01110 :=
  pattern_valid false true true true false

public def selectLogicalXor01111 : Pattern OpCode := pattern false true true true true
public theorem selectLogicalXor01111_valid : Pattern.Valid selectLogicalXor01111 :=
  pattern_valid false true true true true

public def selectLogicalXor10000 : Pattern OpCode := pattern true false false false false
public theorem selectLogicalXor10000_valid : Pattern.Valid selectLogicalXor10000 :=
  pattern_valid true false false false false

public def selectLogicalXor10001 : Pattern OpCode := pattern true false false false true
public theorem selectLogicalXor10001_valid : Pattern.Valid selectLogicalXor10001 :=
  pattern_valid true false false false true

public def selectLogicalXor10010 : Pattern OpCode := pattern true false false true false
public theorem selectLogicalXor10010_valid : Pattern.Valid selectLogicalXor10010 :=
  pattern_valid true false false true false

public def selectLogicalXor10011 : Pattern OpCode := pattern true false false true true
public theorem selectLogicalXor10011_valid : Pattern.Valid selectLogicalXor10011 :=
  pattern_valid true false false true true

public def selectLogicalXor10100 : Pattern OpCode := pattern true false true false false
public theorem selectLogicalXor10100_valid : Pattern.Valid selectLogicalXor10100 :=
  pattern_valid true false true false false

public def selectLogicalXor10101 : Pattern OpCode := pattern true false true false true
public theorem selectLogicalXor10101_valid : Pattern.Valid selectLogicalXor10101 :=
  pattern_valid true false true false true

public def selectLogicalXor10110 : Pattern OpCode := pattern true false true true false
public theorem selectLogicalXor10110_valid : Pattern.Valid selectLogicalXor10110 :=
  pattern_valid true false true true false

public def selectLogicalXor10111 : Pattern OpCode := pattern true false true true true
public theorem selectLogicalXor10111_valid : Pattern.Valid selectLogicalXor10111 :=
  pattern_valid true false true true true

public def selectLogicalXor11000 : Pattern OpCode := pattern true true false false false
public theorem selectLogicalXor11000_valid : Pattern.Valid selectLogicalXor11000 :=
  pattern_valid true true false false false

public def selectLogicalXor11001 : Pattern OpCode := pattern true true false false true
public theorem selectLogicalXor11001_valid : Pattern.Valid selectLogicalXor11001 :=
  pattern_valid true true false false true

public def selectLogicalXor11010 : Pattern OpCode := pattern true true false true false
public theorem selectLogicalXor11010_valid : Pattern.Valid selectLogicalXor11010 :=
  pattern_valid true true false true false

public def selectLogicalXor11011 : Pattern OpCode := pattern true true false true true
public theorem selectLogicalXor11011_valid : Pattern.Valid selectLogicalXor11011 :=
  pattern_valid true true false true true

public def selectLogicalXor11100 : Pattern OpCode := pattern true true true false false
public theorem selectLogicalXor11100_valid : Pattern.Valid selectLogicalXor11100 :=
  pattern_valid true true true false false

public def selectLogicalXor11101 : Pattern OpCode := pattern true true true false true
public theorem selectLogicalXor11101_valid : Pattern.Valid selectLogicalXor11101 :=
  pattern_valid true true true false true

public def selectLogicalXor11110 : Pattern OpCode := pattern true true true true false
public theorem selectLogicalXor11110_valid : Pattern.Valid selectLogicalXor11110 :=
  pattern_valid true true true true false

public def selectLogicalXor11111 : Pattern OpCode := pattern true true true true true
public theorem selectLogicalXor11111_valid : Pattern.Valid selectLogicalXor11111 :=
  pattern_valid true true true true true


end Veir.Passes.InstCombineLLVM.SelectLogicalXor
