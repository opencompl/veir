module

public import Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics
import all Veir.Dialects.LLVM.OpInfo
import all Veir.GlobalOpInfo

namespace Veir.Passes.InstCombineLLVM.ZExtXorAndTruncMask

open Veir Veir.Data Veir.Puddle Veir.Passes.InstCombineLLVM
open Veir.Passes.InstCombineLLVM.CastIntrinsicSemantics

@[local cbv_eval] theorem guard_eq_cond_punit {p : Prop} [Decidable p] :
    (guard p : Option PUnit) = cond (decide p) (some ⟨⟩) none := by
  cases ‹Decidable p› <;> rfl

private def isIntegralConstant
    (props : propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  match (asLLVMConstantProperties props).value with
  | .integer _ => true
  | _ => false

/-- Arbitrary-width scalar instance of InstCombineCasts.cpp:1738-1745. -/
public def zextXorAndTruncMask : Pattern OpCode :=
  Pattern.Builder
    (do
      let wideTy ← MatchProg.type (Attr := IntegerType)
      let narrowTy ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value wideTy
      let trunc ← MatchProg.operation (.llvm .trunc) #[x] #[narrowTy] (fun _ => true)
      let c ← MatchProg.operation (.llvm .mlir__constant) #[] #[narrowTy] isIntegralConstant
      let andOp ← MatchProg.operation (.llvm .and) #[trunc.res[0]!, c.res[0]!]
        #[narrowTy] (fun _ => true)
      let xorOp ← MatchProg.operation (.llvm .xor) #[andOp.res[0]!, c.res[0]!]
        #[narrowTy] (fun _ => true)
      let _ ← MatchProg.root (.llvm .zext) #[xorOp.res[0]!] #[wideTy] (fun _ => true)
      return (wideTy, x, c.res[0]!))
    (fun (wideTy, x, c) => do
      let zp ← CreateProg.property (.llvm .zext) { nneg := false }
      let zc ← CreateProg.operation (.llvm .zext) #[c] #[wideTy] zp
      let ap ← CreateProg.property (.llvm .and) ()
      let andOp ← CreateProg.operation (.llvm .and) #[x, zc.res[0]!] #[wideTy] ap
      let xp ← CreateProg.property (.llvm .xor) ()
      CreateProg.operation (.llvm .xor) #[andOp.res[0]!, zc.res[0]!] #[wideTy] xp)
    (fun result => result.res[0]!)

public theorem zextXorAndTruncMask_valid : Pattern.Valid zextXorAndTruncMask := by
  simp only [zextXorAndTruncMask]
  unfoldPuddleBuilder
  constructor
  · provePuddleSupported
  · open scoped PuddleCbv in cbv
  · open scoped PuddleCbv in cbv <;> simp [guard_eq_cond_punit,
      HandleContext.lookup, HandleContext.lookupBindings, HandleContext.require,
      HandleContext.requireMany, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.insertFreshBindings, CreateDecl.checkBindings,
      Replacement.checkBindings]
  simpPuddleSemantics
  rintro ⟨wideW, wideSignedness⟩ ⟨narrowW, narrowSignedness⟩
  rintro x hX
  obtain ⟨x, rfl⟩ := RuntimeValue.Conforms.integerType.mp hX
  rintro truncProps truncated hTruncated
  obtain ⟨hNarrowWide, rfl⟩ :=
    (trunc_iff wideW narrowW truncProps x truncated).mp hTruncated
  rintro constantProps c hConstant hInterpC
  generalize hTyped : asLLVMConstantProperties constantProps = typedProps
  cases typedProps with
  | mk constantValue => cases constantValue with
    | float _ | dense _ | string _ => simp [isIntegralConstant, hTyped] at hConstant
    | integer attr =>
      have hInterpTyped : InterpretsTo (.llvm .mlir__constant)
          (asLLVMConstantProperties constantProps)
          #[IntegerType.mk narrowW narrowSignedness] #[] #[c] := hInterpC
      rw [hTyped] at hInterpTyped
      obtain rfl := (constant_iff _ attr _).mp hInterpTyped
      rintro ⟨⟩ narrowAnd hNarrowAnd
      obtain rfl := (and_iff _ _ _ _).mp hNarrowAnd
      rintro ⟨⟩ narrowXor hNarrowXor
      obtain rfl := (xor_iff _ _ _ _).mp hNarrowXor
      rintro zextProps source hSource
      obtain ⟨hNarrowWide', rfl⟩ :=
        (zext_iff narrowW wideW zextProps _ source).mp hSource
      refine ⟨.int wideW (LLVM.Int.zext (.val (BitVec.ofInt narrowW attr.value))
        wideW false hNarrowWide), ?_, ?_⟩
      · exact (zext_iff narrowW wideW { nneg := false } _ _).mpr
          ⟨hNarrowWide, rfl⟩
      refine ⟨.int wideW (LLVM.Int.and x (LLVM.Int.zext
        (.val (BitVec.ofInt narrowW attr.value)) wideW false hNarrowWide)),
        (and_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨.int wideW (LLVM.Int.xor
        (LLVM.Int.and x (LLVM.Int.zext (.val (BitVec.ofInt narrowW attr.value))
          wideW false hNarrowWide))
        (LLVM.Int.zext (.val (BitVec.ofInt narrowW attr.value))
          wideW false hNarrowWide)),
        (xor_iff _ _ _ _).mpr rfl, ?_⟩
      refine ⟨rfl, ?_⟩
      simpa only [LLVM.Int.cast_self] using
        zext_xor_and_trunc_mask hNarrowWide x
          (.val (BitVec.ofInt narrowW attr.value))
          truncProps.nsw truncProps.nuw zextProps.nneg

end Veir.Passes.InstCombineLLVM.ZExtXorAndTruncMask

#print axioms Veir.Passes.InstCombineLLVM.ZExtXorAndTruncMask.zextXorAndTruncMask_valid
