module

import all Veir.Dialects.LLVM.OpInfo
import all Veir.Interpreter.Basic
import all Veir.Data.Refinement
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.LLVM.Byte.Basic
public import Veir.Interpreter.Lemmas
public import Veir.Data.LLVM.Byte.Lemmas

public section

/-!
# Monotonicity of the LLVM interpreter

An LLVM opcode is monotone in its operands when a more defined operand cannot change what the
opcode does, beyond making its result more defined. Every opcode here is, except the ones
`Llvm.isMonotone` rules out:

* `freeze` turns poison into zero, so a more defined operand gives a *different* result;
* `store` writes a poison byte where a refined operand writes a concrete one, which the relation
  rejects because it asks for the two memories to be equal rather than refined;
* `shl`, `lshr` and `bitcast` read a byte, and refinement of bytes is bit by bit, which needs
  shift and conversion lemmas that `Veir.Data.LLVM.Byte` does not have yet;
* `switch` picks its successor inside a loop, so relating the two runs needs an induction over
  that loop.
-/

open Veir.Data
open Veir.Data.LLVM

namespace Veir

/-- Whether this file proves the opcode monotone. Reducible, so that instance search can
decide it for a concrete opcode. -/
@[reducible, expose]
def Llvm.isMonotone : Llvm → Bool
  | .freeze | .store | .shl | .lshr | .bitcast | .switch => false
  | _ => true

set_option hygiene false in
/-- An arm that reads two integer operands of the same width. -/
local macro "int_binary " mono:term : tactic => `(tactic| (
  split
  case _ bw lhs bw' rhs hOps =>
    obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := RuntimeValue.arrayIsRefinedBy_toList_pair hOps h
    obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy h₁
    obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy h₂
    rw [hw]
    dsimp only
    split
    · simp [Interp.isRefinedBy]
    · exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy $mono)
  case _ => simp [Interp.isRefinedBy]))

set_option hygiene false in
/-- An arm that reads one integer operand. -/
local macro "int_unary " mono:term : tactic => `(tactic| (
  split
  case _ bw x hOps =>
    obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
    obtain ⟨x', rfl, hx⟩ := RuntimeValue.int_of_isRefinedBy h₁
    rw [hw]
    dsimp only
    exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy $mono)
  case _ => simp [Interp.isRefinedBy]))

set_option hygiene false in
/-- An arm that reads two integer operands and may be undefined behaviour. -/
local macro "int_binary_ub " ub:term ", " mono:term : tactic => `(tactic| (
  split
  case _ bw lhs bw' rhs hOps =>
    obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := RuntimeValue.arrayIsRefinedBy_toList_pair hOps h
    obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy h₁
    obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy h₂
    rw [hw]
    dsimp only
    split
    · simp [Interp.isRefinedBy]
    · split
      · simp [Interp.isRefinedBy]
      · next hub =>
        rw [$ub (by simpa using hub)]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy $mono)
  case _ => simp [Interp.isRefinedBy]))

set_option hygiene false in
/-- An arm that reads three integer operands of the same width. -/
local macro "int_ternary " mono:term : tactic => `(tactic| (
  split
  case _ bw a bw' b bw'' c hOps =>
    obtain ⟨w₁, w₂, w₃, hw, h₁, h₂, h₃⟩ := RuntimeValue.arrayIsRefinedBy_toList_triple hOps h
    obtain ⟨a', rfl, ha⟩ := RuntimeValue.int_of_isRefinedBy h₁
    obtain ⟨b', rfl, hb⟩ := RuntimeValue.int_of_isRefinedBy h₂
    obtain ⟨c', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy h₃
    rw [hw]
    dsimp only
    split
    · simp [Interp.isRefinedBy]
    · split
      · simp [Interp.isRefinedBy]
      · exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy $mono)
  case _ => simp [Interp.isRefinedBy]))

theorem Llvm.interpretOp'_monotone {op : Llvm} (hMono : op.isMonotone)
    (properties : propertiesOf op) (resultTypes : Array TypeAttr)
    {operands operands' : Array RuntimeValue} (blockOperands : Array BlockPtr)
    (mem : MemoryState) (layout : DataLayout) (h : operands ⊒ operands') :
    Interp.isRefinedBy OperationResult.isRefinedBy
      (Llvm.interpretOp' op properties resultTypes operands blockOperands mem layout)
      (Llvm.interpretOp' op properties resultTypes operands' blockOperands mem layout) := by
  cases op <;> simp only [Llvm.interpretOp'] <;>
    try exact Interp.isRefinedBy_refl_operationResult _
  case udiv =>
    int_binary_ub (fun hub => Data.LLVM.Int.isUnsignedDivisionUB_eq_false_mono
      (Int.cast_mono _ _ _ hr) hub), (Int.udiv_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr) _)
  case «return» =>
    exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, h⟩
  case br =>
    split
    case _ dest hDest =>
      exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, rfl, h⟩
    case _ => simp [Interp.isRefinedBy]
  case alloca =>
    split
    case _ bw count hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      obtain ⟨count', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy h₁
      obtain rfl : count' = .val count := by
        cases count' <;> simp_all [isRefinedBy]
      simp only [hw]
      exact Interp.isRefinedBy_refl_operationResult _
    case _ => simp [Interp.isRefinedBy]
  case load =>
    split
    · split
      · next ptr hOps =>
        obtain ⟨w, hw, hRef⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
        obtain rfl : w = .addr (.val ptr) := by
          grind [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy,
            cases RuntimeValue, cases Data.LLVM.Ptr]
        rw [hw]
        exact Interp.isRefinedBy_refl_operationResult _
      · simp [Interp.isRefinedBy]
    · simp [Interp.isRefinedBy]
  case getelementptr =>
    split
    case _ ptr bw idx hOps =>
      obtain ⟨w₁, w₂, hw, h₁, h₂⟩ := RuntimeValue.arrayIsRefinedBy_toList_pair hOps h
      obtain ⟨idx', rfl, hi⟩ := RuntimeValue.int_of_isRefinedBy h₂
      obtain ⟨p', rfl⟩ : ∃ p', w₁ = .addr p' := by
        cases w₁ <;> simp_all [RuntimeValue.isRefinedBy]
      simp only [hw]
      refine Interp.isRefinedBy_bind_same _ (fun size => ?_)
      cases ptr
      case poison =>
        cases p' <;> cases idx' <;>
          refine OperationResult.isRefinedBy_value ?_ <;>
          simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]
      case val p =>
        obtain rfl : p' = .val p := by
          simp only [RuntimeValue.isRefinedBy] at h₁
          cases p' <;> simp_all [Data.LLVM.Ptr.isRefinedBy]
        cases idx
        case poison =>
          cases idx' <;>
            refine OperationResult.isRefinedBy_value ?_ <;>
            simp [RuntimeValue.isRefinedBy, Data.LLVM.Ptr.isRefinedBy]
        case val v =>
          obtain rfl : idx' = .val v := by cases idx' <;> simp_all [isRefinedBy]
          exact Interp.isRefinedBy_refl_operationResult _
    case _ => simp [Interp.isRefinedBy]
  case trunc =>
    split
    case _ val hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      cases val
      case int bw v =>
        obtain ⟨v', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h₁
        simp only [hw]
        split
        case _ resType hres =>
          obtain ⟨attr, hattr⟩ := resType
          cases attr <;> try exact Interp.isRefinedBy_fail_target
          case integerType ty =>
            by_cases hle : ty.bitwidth ≥ bw
            · simp [hle, Interp.isRefinedBy]
            · simp only [hle, ↓reduceDIte]
              exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy
                (Int.trunc_mono _ _ _ hv))
        case _ => simp [Interp.isRefinedBy]
      case byte bw v =>
        obtain ⟨v', rfl, hv⟩ := RuntimeValue.byte_of_isRefinedBy h₁
        simp only [hw]
        split
        case _ resType hres =>
          obtain ⟨attr, hattr⟩ := resType
          cases attr <;> try exact Interp.isRefinedBy_fail_target
          case byteType ty =>
            by_cases hle : ty.bitwidth ≥ bw
            · simp [hle, Interp.isRefinedBy]
            · simp only [hle, ↓reduceDIte]
              exact OperationResult.isRefinedBy_value (RuntimeValue.byte_isRefinedBy
                (Data.LLVM.Byte.trunc_mono hv))
        case _ => simp [Interp.isRefinedBy]
      all_goals (split <;> simp [Interp.isRefinedBy])
    case _ => simp [Interp.isRefinedBy]
  case cond_br =>
    split
    case _ destTrue destFalse hDest =>
      split
      case _ condVal hCond =>
        obtain ⟨w, hw, hRef⟩ := RuntimeValue.getElem?_of_arrayIsRefinedBy h hCond
        simp only [hw]
        split
        case _ trueSize hSize =>
          rcases condVal with _ | _ | _ | _ | _ | _
          case int bw v =>
            match bw, v with
            | 1, .val c =>
              obtain ⟨c', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy hRef
              obtain rfl : c' = .val c := by cases c' <;> simp_all [isRefinedBy]
              by_cases hcond : c = 1#1
              · simp only [hcond, ↓reduceIte]
                exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, rfl,
                  RuntimeValue.arrayIsRefinedBy_extract h _ _⟩
              · simp only [hcond, ↓reduceIte]
                exact ⟨⟨rfl, fun i hi => by simp at hi⟩, rfl, rfl,
                  RuntimeValue.arrayIsRefinedBy_extract_from h _⟩
            | 1, .poison => simp [Interp.isRefinedBy]
            | 0, _ | (_ + 2), _ => simp [Interp.isRefinedBy]
          all_goals simp [Interp.isRefinedBy]
        case _ => simp [Interp.isRefinedBy]
      case _ => simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]
  case select =>
    split
    case _ cond bw lhs bw' rhs hOps =>
      obtain ⟨w₁, w₂, w₃, hw, h₁, h₂, h₃⟩ := RuntimeValue.arrayIsRefinedBy_toList_triple hOps h
      obtain ⟨cond', rfl, hc⟩ := RuntimeValue.int_of_isRefinedBy h₁
      obtain ⟨lhs', rfl, hl⟩ := RuntimeValue.int_of_isRefinedBy h₂
      obtain ⟨rhs', rfl, hr⟩ := RuntimeValue.int_of_isRefinedBy h₃
      simp only [hw]
      split
      · simp [Interp.isRefinedBy]
      · exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy
          (Int.select_mono _ _ _ _ _ _ hl (Int.cast_mono _ _ _ hr) hc))
    case _ => simp [Interp.isRefinedBy]
  case zext =>
    split
    case _ w val hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      obtain ⟨val', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h₁
      simp only [hw]
      split
      case _ resType hres =>
        obtain ⟨attr, hattr⟩ := resType
        cases attr <;> try exact Interp.isRefinedBy_fail_target
        split <;> try split
        all_goals first
          | exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy
              (Int.zext_mono _ _ _ hv))
          | simp [Interp.isRefinedBy]
      case _ => simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]
  case sext =>
    split
    case _ w val hOps =>
      obtain ⟨w₁, hw, h₁⟩ := RuntimeValue.arrayIsRefinedBy_toList_singleton hOps h
      obtain ⟨val', rfl, hv⟩ := RuntimeValue.int_of_isRefinedBy h₁
      simp only [hw]
      split
      case _ resType hres =>
        obtain ⟨attr, hattr⟩ := resType
        cases attr <;> try exact Interp.isRefinedBy_fail_target
        split <;> try split
        all_goals first
          | exact OperationResult.isRefinedBy_value (RuntimeValue.int_isRefinedBy
              (Int.sext_mono _ _ _ hv))
          | simp [Interp.isRefinedBy]
      case _ => simp [Interp.isRefinedBy]
    case _ => simp [Interp.isRefinedBy]
  case sdiv =>
    int_binary_ub (fun hub => Data.LLVM.Int.isSignedDivisionUB_eq_false_mono
      hl (Int.cast_mono _ _ _ hr) hub), (Int.sdiv_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr) _)
  case srem =>
    int_binary_ub (fun hub => Data.LLVM.Int.isSignedDivisionUB_eq_false_mono
      hl (Int.cast_mono _ _ _ hr) hub), (Int.srem_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case urem =>
    int_binary_ub (fun hub => Data.LLVM.Int.isUnsignedDivisionUB_eq_false_mono
      (Int.cast_mono _ _ _ hr) hub), (Int.urem_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__fshl =>
    int_ternary (Int.fshl_mono _ _ _ _ _ _ ha (Int.cast_mono _ _ _ hb) (Int.cast_mono _ _ _ hc))
  case intr__fshr =>
    int_ternary (Int.fshr_mono _ _ _ _ _ _ ha (Int.cast_mono _ _ _ hb) (Int.cast_mono _ _ _ hc))
  case add => int_binary (Int.add_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr) _ _)
  case sub => int_binary (Int.sub_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr) _ _)
  case mul => int_binary (Int.mul_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr) _ _)
  case ashr => int_binary (Int.ashr_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr) _)
  case and => int_binary (Int.and_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case or => int_binary (Int.or_mono _ _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case xor => int_binary (Int.xor_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case icmp => int_binary (Int.icmp_mono _ _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__smax => int_binary (Int.smax_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__smin => int_binary (Int.smin_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__umax => int_binary (Int.umax_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__umin => int_binary (Int.umin_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__sadd__sat => int_binary (Int.saddSat_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__uadd__sat => int_binary (Int.uaddSat_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__ssub__sat => int_binary (Int.ssubSat_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__usub__sat => int_binary (Int.usubSat_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__sshl__sat => int_binary (Int.sshlSat_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__ushl__sat => int_binary (Int.ushlSat_mono _ _ _ _ hl (Int.cast_mono _ _ _ hr))
  case intr__ctlz => int_unary (Int.ctlz_mono _ _ _ hx)
  case intr__cttz => int_unary (Int.cttz_mono _ _ _ hx)
  case intr__ctpop => int_unary (Int.ctpop_mono _ _ hx)
  case intr__bswap => int_unary (Int.bswap_mono _ _ hx)
  case intr__bitreverse => int_unary (Int.bitreverse_mono _ _ hx)
  case intr__abs => int_unary (Int.abs_mono _ _ _ hx)
  all_goals simp [Llvm.isMonotone] at hMono

/-- A boolean side condition on an instance, discharged by reduction for a concrete opcode. -/
class IsTrue (b : Bool) : Prop where
  out : b = true

instance : IsTrue true := ⟨rfl⟩

instance (op : Llvm) [hMono : IsTrue (Llvm.isMonotone op)] : InterpretOp'Monotone (.llvm op) where
  monotone properties resultTypes operands operands' blockOperands mem h := by
    simp only [interpretOp']
    exact Llvm.interpretOp'_monotone hMono.out properties resultTypes blockOperands mem _ h

end Veir

end
