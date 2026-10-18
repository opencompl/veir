module

public import Veir.PatternRewriter.Puddle.Validity
public import Veir.Data.LLVM.Int.Lemmas
import all Veir.Data.LLVM.Int.Basic
import all Veir.Data.Refinement

namespace Veir.Passes.InstCombineLLVM

open Veir
open Veir.Data
open Veir.Puddle

public theorem mlir_poison_eq (w : Nat) :
    LLVM.Int.mlir_poison w = .poison := by rfl

/-- Expose the concrete property record behind the opcode-indexed `llvm.mlir.constant` family.
    Keeping this conversion named avoids Lean 4.35 elaboration failures after Puddle exports a
    constant property handle to a creator. -/
@[expose] public def asLLVMConstantProperties
    (properties : propertiesOf (OpCode.llvm .mlir__constant)) : LLVMConstantProperties :=
  properties

/-- Match a scalar LLVM integer constant by mathematical value.
    The operation result handle already fixes the SSA result type. -/
@[expose] public def matchIntConstant (ty : Handle OpCode .type) (value : Int) :
  MatchProg.Builder (Handle OpCode .value) := do
  let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] fun properties =>
    match properties.value with
    | .integer attr => attr.value = value
    | _ => false
  return constant.res[0]!

/-- Match the bit pattern of a scalar LLVM integer constant at the matched SSA type.
    Unlike `matchIntConstant`, this accepts every parser-normalized spelling of the
    same APInt, including signless `i1 true` (stored as `1`) for all-ones (`-1`). -/
@[expose] public def isNormalizedIntConstant
    (value : Int)
    (input : TypeAttr × propertiesOf (OpCode.llvm .mlir__constant)) : Bool :=
  let (type, properties) := input
  match type.cast? IntegerType, (asLLVMConstantProperties properties).value with
  | some intType, .integer attr =>
      BitVec.ofInt intType.bitwidth attr.value == BitVec.ofInt intType.bitwidth value
  | _, _ => false

@[expose] public def matchIntConstantNormalized
    (ty : Handle OpCode .type) (value : Int) :
    MatchProg.Builder (Handle OpCode .value) := do
  let constant ← MatchProg.operation (.llvm .mlir__constant) #[] #[ty] (fun _ => true)
  MatchProg.matchNative (ty, constant.properties) (isNormalizedIntConstant value)
  return constant.res[0]!

public theorem constant_iff (ty : IntegerType) (attr : IntegerAttr) (v : RuntimeValue) :
    InterpretsTo (.llvm .mlir__constant) (LLVMConstantProperties.mk (.integer attr))
      #[ty] #[] #[v] ↔
      v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth attr.value)) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq,
    Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and,
    interpretOp', Llvm.interpretOp', List.getElem_toArray, TypeAttr.of_val, Interp.pure_eq]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind


public theorem ofInt_normalizeValue (ty : IntegerType) (value : Int) :
    BitVec.ofInt ty.bitwidth (IntegerAttr.normalizeValue ty value) =
      BitVec.ofInt ty.bitwidth value := by
  unfold IntegerAttr.normalizeValue
  split
  · rw [BitVec.ofInt_natCast, BitVec.ofNat_toNat]
    simp
  · rw [BitVec.ofInt_toInt]

public theorem add_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .add : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .add) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.add x y props.nsw props.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem mul_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .mul : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .mul) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.mul x y props.nsw props.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem sub_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .sub : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .sub) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.sub x y props.nsw props.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem lshr_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .lshr : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .lshr) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.lshr x y props.exact) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem ashr_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .ashr : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .ashr) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.ashr x y props.exact) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem xor_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .xor) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.xor x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem and_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .and) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.and x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem or_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .or : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .or) props #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.or x y props.disjoint) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem smax_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__smax) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.smax x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem smin_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__smin) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.smin x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem umax_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__umax) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.umax x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem umin_iff {signedness : IntegerType.Signedness} (w : Nat)
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__umin) () #[IntegerType.mk w signedness]
      #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.umin x y) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', ne_eq, not_true_eq_false, ↓reduceDIte, LLVM.Int.cast_self,
    Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq, Array.mk.injEq,
    List.cons.injEq, and_true, TypeAttr.of_val]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem ctlz_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__ctlz : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__ctlz) props #[IntegerType.mk w signedness]
      #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.ctlz x props.is_zero_poison) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

public theorem cttz_iff {signedness : IntegerType.Signedness} (w : Nat)
    (props : propertiesOf (.llvm .intr__cttz : OpCode))
    (x : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.llvm .intr__cttz) props #[IntegerType.mk w signedness]
      #[.int w x] #[v] ↔
      v = .int w (LLVM.Int.cttz x props.is_zero_poison) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms,
    List.getElem!_toArray, List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one,
    getElem?_pos, List.getElem_cons_zero, Option.getD_some, true_and, interpretOp',
    Llvm.interpretOp', Interp.pure_eq, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    exact (h .empty).symm
  · grind

/-- Normalize the underlying attribute of a scalar integer type.  The LLVM extension
    interpreter inspects this value directly when selecting the destination width. -/
public theorem integerType_of_val (t : IntegerType) :
    (TypeAttr.of IntegerType t).val = .integerType t := by
  rw [TypeAttr.of_val]
  exact (Attribute.integerType_eq_of t).symm

public theorem zext_iff {signedness : IntegerType.Signedness} (w₁ w₂ : Nat)
    (props : propertiesOf (.llvm .zext : OpCode))
    (x : LLVM.Int w₁) (v : RuntimeValue) :
    InterpretsTo (.llvm .zext) props #[IntegerType.mk w₂ signedness]
      #[.int w₁ x] #[v] ↔
      ∃ h : w₁ < w₂, v = .int w₂ (LLVM.Int.zext x w₂ props.nneg h) := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)) := by
    rfl
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val] at hv
    split at hv
    · contradiction
    · exact ⟨by omega, by simpa using hv.symm⟩
  · rintro ⟨hw, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val]
      have hn : ¬w₂ ≤ w₁ := by omega
      simp [hn]

public theorem sext_iff {signedness : IntegerType.Signedness} (w₁ w₂ : Nat)
    (x : LLVM.Int w₁) (v : RuntimeValue) :
    InterpretsTo (.llvm .sext) () #[IntegerType.mk w₂ signedness]
      #[.int w₁ x] #[v] ↔
      ∃ h : w₁ < w₂, v = .int w₂ (LLVM.Int.sext x w₂ h) := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)) := by
    rfl
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val] at hv
    split at hv
    · contradiction
    · exact ⟨by omega, by simpa using hv.symm⟩
  · rintro ⟨hw, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val]
      have hn : ¬w₂ ≤ w₁ := by omega
      simp [hn]

public theorem trunc_iff {signedness : IntegerType.Signedness} (w₁ w₂ : Nat)
    (props : propertiesOf (.llvm .trunc : OpCode))
    (x : LLVM.Int w₁) (v : RuntimeValue) :
    InterpretsTo (.llvm .trunc) props #[IntegerType.mk w₂ signedness]
      #[.int w₁ x] #[v] ↔
      ∃ h : w₂ < w₁, v = .int w₂ (LLVM.Int.trunc x w₂ props.nsw props.nuw h) := by
  have hResultType :
      (#[TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)][0]? : Option TypeAttr) =
        some (TypeAttr.of IntegerType (IntegerType.mk w₂ signedness)) := by
    rfl
  simp only [InterpretsTo]
  constructor
  · rintro ⟨_, hi⟩
    have hv := hi .empty
    simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val] at hv
    split at hv
    · contradiction
    · exact ⟨by omega, by simpa using hv.symm⟩
  · rintro ⟨hw, rfl⟩
    constructor
    · simp
    · intro memory
      simp only [interpretOp', Llvm.interpretOp', hResultType, integerType_of_val]
      have hn : ¬w₁ ≤ w₂ := by omega
      simp [hn]

public theorem neg_sext_i1 (w : Nat) (h : 1 < w) (x : LLVM.Int 1) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.sext x w h) =
      LLVM.Int.zext x w false h := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.sext, LLVM.Int.zext, Id.run]
  | val x =>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
      simp [LLVM.Int.sub, LLVM.Int.sext, LLVM.Int.zext, Id.run,
        BitVec.signExtend_eq_setWidth_of_msb_false,
        BitVec.signExtend_eq_not_setWidth_not_of_msb_true]
    · rw [← BitVec.neg_one_eq_allOnes]
      simp [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt]

public theorem neg_zext_i1 (w : Nat) (h : 1 < w) (x : LLVM.Int 1) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.zext x w false h) =
      LLVM.Int.sext x w h := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.sext, LLVM.Int.zext, Id.run]
  | val x =>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
      simp [LLVM.Int.sub, LLVM.Int.sext, LLVM.Int.zext, Id.run,
        BitVec.signExtend_eq_setWidth_of_msb_false,
        BitVec.signExtend_eq_not_setWidth_not_of_msb_true]
    · rw [BitVec.setWidth_ofNat_one_eq_ofNat_one_of_lt (by decide)]
      exact BitVec.neg_one_eq_allOnes

public theorem zext_nneg_refines (w : Nat) (h : 1 < w) (x : LLVM.Int 1) (nneg : Bool) :
    LLVM.Int.zext x w nneg h ⊒ LLVM.Int.zext x w false h := by
  cases x with
  | poison => simp [LLVM.Int.zext, Id.run, isRefinedBy]
  | val x =>
    cases nneg
    · exact isRefinedBy_refl _
    · by_cases hx : x.msb = true
      · simp [LLVM.Int.zext, Id.run, hx, isRefinedBy, pure]
      · simp [LLVM.Int.zext, Id.run, hx, isRefinedBy]

theorem bitvec_ashr_top {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x.sshiftRight (w - 1) = if x.msb then BitVec.allOnes w else 0 := by
  apply BitVec.eq_of_toNat_eq
  by_cases hmsb : x.msb = true
  · rw [ite_eq_left hmsb, BitVec.toNat_allOnes,
      BitVec.toNat_sshiftRight_of_msb_true hmsb]
    have hle := BitVec.le_toNat_of_msb_true hmsb
    have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
      calc
        2 ^ w = 2 ^ ((w - 1) + 1) := by congr 1 <;> omega
        _ = 2 * 2 ^ (w - 1) := by rw [Nat.pow_add_one]; omega
    have hsmall : 2 ^ w - 1 - x.toNat < 2 ^ (w - 1) := by omega
    rw [Nat.shiftRight_eq_zero _ _ hsmall]
    omega
  · rw [Bool.not_eq_true] at hmsb
    have hfalse : x.msb = false := hmsb
    rw [ite_eq_right (by simpa using hmsb), show (0 : BitVec w).toNat = 0 by simp,
      BitVec.toNat_sshiftRight_of_msb_false hfalse]
    exact Nat.shiftRight_eq_zero _ _ (BitVec.toNat_lt_of_msb_false hfalse)

theorem bitvec_lshr_top {w : Nat} (hw : 0 < w) (x : BitVec w) :
    x >>> (w - 1) = if x.msb then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  by_cases hmsb : x.msb = true
  · rw [ite_eq_left hmsb, show (1 : BitVec w).toNat = 1 by simp [hw],
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    apply Nat.div_eq_of_lt_le
    · simpa using BitVec.le_toNat_of_msb_true hmsb
    · have hx := x.isLt
      have hpow : 2 ^ w = 2 * 2 ^ (w - 1) := by
        calc
          2 ^ w = 2 ^ ((w - 1) + 1) := by congr 1 <;> omega
          _ = 2 * 2 ^ (w - 1) := by rw [Nat.pow_add_one]; omega
      rw [hpow] at hx
      simpa [Nat.mul_comm] using hx
  · rw [Bool.not_eq_true] at hmsb
    have hfalse : x.msb = false := hmsb
    rw [ite_eq_right (by simpa using hmsb), show (0 : BitVec w).toNat = 0 by simp,
      BitVec.toNat_ushiftRight]
    exact Nat.shiftRight_eq_zero _ _ (BitVec.toNat_lt_of_msb_false hfalse)

theorem top_shift_amount_toNat {w : Nat} (hw : 0 < w) :
    (BitVec.ofInt w (Int.ofNat (w - 1))).toNat = w - 1 := by
  change (BitVec.ofNat w (w - 1)).toNat = w - 1
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  exact Nat.lt_of_le_of_lt (Nat.sub_le w 1) (Nat.lt_pow_self (a := 2) (by decide))

public theorem neg_ashr_top (w : Nat) (x : LLVM.Int w) (exactFlag : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.ashr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exactFlag) =
      LLVM.Int.lshr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exactFlag := by
  rcases w with _ | w
  · cases x <;> simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure]
  · cases x with
    | poison => simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run]
    | val x =>
      have hneg : -(x.sshiftRight w) = x >>> w := by
        simpa using (show -(x.sshiftRight ((w + 1) - 1)) = x >>> ((w + 1) - 1) by
          rw [bitvec_ashr_top (by omega), bitvec_lshr_top (by omega)]
          split
          · rw [← BitVec.neg_one_eq_allOnes]; simp
          · simp)
      have hmod : w % 2 ^ (w + 1) = w := Nat.mod_eq_of_lt
        (Nat.lt_trans (Nat.lt_succ_self w) (Nat.lt_pow_self (a := 2) (by decide)))
      have hlt : ¬w + 1 ≤ w := by omega
      cases exactFlag
      · simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure,
          BitVec.le_def, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
          top_shift_amount_toNat (w := w + 1) (by omega), hmod, hlt, hneg]
      · by_cases hexact : (x >>> w) <<< w ≠ x
        · simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure,
            BitVec.le_def, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
            BitVec.shiftLeft_eq', top_shift_amount_toNat (w := w + 1) (by omega),
            hmod, hlt, hexact]
        · simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure,
            BitVec.le_def, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
            BitVec.shiftLeft_eq', top_shift_amount_toNat (w := w + 1) (by omega),
            hmod, hlt, hexact, hneg]

public theorem neg_lshr_top (w : Nat) (x : LLVM.Int w) (exactFlag : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.lshr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exactFlag) =
      LLVM.Int.ashr x (.val (BitVec.ofInt w (Int.ofNat (w - 1)))) exactFlag := by
  rcases w with _ | w
  · cases x <;> simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure]
  · cases x with
    | poison => simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run]
    | val x =>
      have hneg : -(x >>> w) = x.sshiftRight w := by
        simpa using (show -(x >>> ((w + 1) - 1)) = x.sshiftRight ((w + 1) - 1) by
          rw [bitvec_ashr_top (by omega), bitvec_lshr_top (by omega)]
          split <;> simp [BitVec.neg_one_eq_allOnes])
      have hmod : w % 2 ^ (w + 1) = w := Nat.mod_eq_of_lt
        (Nat.lt_trans (Nat.lt_succ_self w) (Nat.lt_pow_self (a := 2) (by decide)))
      have hlt : ¬w + 1 ≤ w := by omega
      cases exactFlag
      · simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure,
          BitVec.le_def, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
          top_shift_amount_toNat (w := w + 1) (by omega), hmod, hlt, hneg]
      · by_cases hexact : (x >>> w) <<< w ≠ x
        · simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure,
            BitVec.le_def, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
            BitVec.shiftLeft_eq', top_shift_amount_toNat (w := w + 1) (by omega),
            hmod, hlt, hexact]
        · simp [LLVM.Int.sub, LLVM.Int.ashr, LLVM.Int.lshr, Id.run, pure,
            BitVec.le_def, BitVec.ushiftRight_eq', BitVec.sshiftRight_eq',
            BitVec.shiftLeft_eq', top_shift_amount_toNat (w := w + 1) (by omega),
            hmod, hlt, hexact, hneg]

public theorem neg_increment (w : Nat) (x : LLVM.Int w) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.add x (.val (BitVec.ofInt w 1))) =
      LLVM.Int.xor x (.val (BitVec.ofInt w (-1))) := by
  cases x <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run, pure]
  rw [BitVec.neg_eq_not_add, BitVec.not_add_one]
  rw [BitVec.sub_add_cancel]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]

public theorem add_flags_refine (w : Nat) (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw ⊒ LLVM.Int.add x y := by
  cases x with
  | poison => simp [LLVM.Int.add, isRefinedBy, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.add, isRefinedBy, Id.run]
    | val y =>
      by_cases hs : x.saddOverflow y = true
      <;> by_cases hu : x.uaddOverflow y = true
      <;> cases nsw <;> cases nuw
      <;> simp [LLVM.Int.add, hs, hu, isRefinedBy, Id.run, pure]

public theorem sub_flags_refine (w : Nat) (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.sub x y nsw nuw ⊒ LLVM.Int.sub x y := by
  cases x with
  | poison => simp [LLVM.Int.sub, isRefinedBy, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.sub, isRefinedBy, Id.run]
    | val y =>
      by_cases hs : x.ssubOverflow y = true
      <;> by_cases hu : x.usubOverflow y = true
      <;> cases nsw <;> cases nuw
      <;> simp [LLVM.Int.sub, hs, hu, isRefinedBy, Id.run, pure]

public theorem zero_sub_poison (w : Nat) (nsw nuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0)) .poison nsw nuw = .poison := by
  simp [LLVM.Int.sub, Id.run]

public theorem shl_flags_refine (w : Nat) (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.shl x y nsw nuw ⊒ LLVM.Int.shl x y := by
  cases w with
  | zero =>
    cases x <;> cases y <;> cases nsw <;> cases nuw <;>
      simp [LLVM.Int.shl, isRefinedBy, Id.run, pure, BitVec.le_def]
  | succ w =>
    have hmod : (w + 1) % 2 ^ (w + 1) = w + 1 := Nat.mod_eq_of_lt
      (Nat.lt_pow_self (a := 2) (by omega))
    cases x with
    | poison => simp [LLVM.Int.shl, isRefinedBy, Id.run]
    | val x =>
      cases y with
      | poison => simp [LLVM.Int.shl, isRefinedBy, Id.run]
      | val y =>
        by_cases hle : w + 1 ≤ y.toNat
        · cases nsw <;> cases nuw <;>
            simp [LLVM.Int.shl, isRefinedBy, Id.run, pure, BitVec.le_def, hmod, hle]
        · have hlt : y.toNat < w + 1 := by omega
          by_cases hs : (x <<< y.toNat).sshiftRight y.toNat = x
          <;> by_cases hu : (x <<< y.toNat) >>> y.toNat = x
          <;> cases nsw <;> cases nuw
          <;> simp [LLVM.Int.shl, isRefinedBy, Id.run, pure, BitVec.le_def,
            BitVec.sshiftRight_eq', BitVec.ushiftRight_eq', hmod, hle, hlt, hs, hu]

public theorem mul_flags_refine (w : Nat) (x y : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.mul x y nsw nuw ⊒ LLVM.Int.mul x y := by
  cases x with
  | poison => simp [LLVM.Int.mul, isRefinedBy, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.mul, isRefinedBy, Id.run]
    | val y =>
      by_cases hs : x.smulOverflow y = true
      <;> by_cases hu : x.umulOverflow y = true
      <;> cases nsw <;> cases nuw
      <;> simp [LLVM.Int.mul, hs, hu, isRefinedBy, Id.run, pure]

public theorem i1_add_eq_xor (x y : LLVM.Int 1) :
    LLVM.Int.add x y = LLVM.Int.xor x y := by
  cases x with
  | poison => simp [LLVM.Int.add, LLVM.Int.xor, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.add, LLVM.Int.xor, Id.run]
    | val y =>
      rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
        rcases BitVec.eq_zero_or_eq_one y with rfl | rfl <;>
        simp [LLVM.Int.add, LLVM.Int.xor, Id.run]

public theorem i1_add_refines_xor (x y : LLVM.Int 1) (nsw nuw : Bool) :
    LLVM.Int.add x y nsw nuw ⊒ LLVM.Int.xor x y := by
  apply isRefinedBy_trans (add_flags_refine 1 x y nsw nuw)
  rw [i1_add_eq_xor]
  exact isRefinedBy_refl _

public theorem i1_sub_eq_xor (x y : LLVM.Int 1) :
    LLVM.Int.sub x y = LLVM.Int.xor x y := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.xor, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.sub, LLVM.Int.xor, Id.run]
    | val y =>
      rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
        rcases BitVec.eq_zero_or_eq_one y with rfl | rfl <;>
        simp [LLVM.Int.sub, LLVM.Int.xor, Id.run]

public theorem i1_sub_refines_xor (x y : LLVM.Int 1) (nsw nuw : Bool) :
    LLVM.Int.sub x y nsw nuw ⊒ LLVM.Int.xor x y := by
  apply isRefinedBy_trans (sub_flags_refine 1 x y nsw nuw)
  rw [i1_sub_eq_xor]
  exact isRefinedBy_refl _

public theorem i1_umin_eq_and (x y : LLVM.Int 1) :
    LLVM.Int.umin x y = LLVM.Int.and x y := by
  cases x with
  | poison => simp [LLVM.Int.umin, LLVM.Int.and, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.umin, LLVM.Int.and, Id.run]
    | val y =>
      rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
        rcases BitVec.eq_zero_or_eq_one y with rfl | rfl <;>
        simp [LLVM.Int.umin, LLVM.Int.and, Id.run, BitVec.ule]

public theorem i1_smax_eq_and (x y : LLVM.Int 1) :
    LLVM.Int.smax x y = LLVM.Int.and x y := by
  cases x with
  | poison => simp [LLVM.Int.smax, LLVM.Int.and, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.smax, LLVM.Int.and, Id.run]
    | val y =>
      rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
        rcases BitVec.eq_zero_or_eq_one y with rfl | rfl <;>
        simp [LLVM.Int.smax, LLVM.Int.and, Id.run, BitVec.sle]

public theorem i1_umax_eq_or (x y : LLVM.Int 1) :
    LLVM.Int.umax x y = LLVM.Int.or x y := by
  cases x with
  | poison => simp [LLVM.Int.umax, LLVM.Int.or, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.umax, LLVM.Int.or, Id.run]
    | val y =>
      rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
        rcases BitVec.eq_zero_or_eq_one y with rfl | rfl <;>
        simp [LLVM.Int.umax, LLVM.Int.or, Id.run, BitVec.ule]

public theorem i1_smin_eq_or (x y : LLVM.Int 1) :
    LLVM.Int.smin x y = LLVM.Int.or x y := by
  cases x with
  | poison => simp [LLVM.Int.smin, LLVM.Int.or, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.smin, LLVM.Int.or, Id.run]
    | val y =>
      rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
        rcases BitVec.eq_zero_or_eq_one y with rfl | rfl <;>
        simp [LLVM.Int.smin, LLVM.Int.or, Id.run, BitVec.sle]

public theorem i1_ctlz_false_eq_not (x : LLVM.Int 1) :
    LLVM.Int.ctlz x false = LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1))) := by
  cases x with
  | poison => simp [LLVM.Int.ctlz, LLVM.Int.xor, Id.run]
  | val x =>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
      simp [LLVM.Int.ctlz, LLVM.Int.xor, Id.run, BitVec.clz,
        BitVec.neg_one_eq_allOnes] <;> decide

public theorem i1_cttz_false_eq_not (x : LLVM.Int 1) :
    LLVM.Int.cttz x false = LLVM.Int.xor x (.val (BitVec.ofInt 1 (-1))) := by
  cases x with
  | poison => simp [LLVM.Int.cttz, LLVM.Int.xor, Id.run]
  | val x =>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
      simp [LLVM.Int.cttz, LLVM.Int.xor, Id.run, BitVec.ctz,
        BitVec.neg_one_eq_allOnes] <;> decide

public theorem i1_ctlz_true_refines_zero (x : LLVM.Int 1) :
    LLVM.Int.ctlz x true ⊒ (.val (BitVec.ofInt 1 0)) := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val x =>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
      simp [LLVM.Int.ctlz, Id.run, pure, isRefinedBy, BitVec.clz] <;> decide

public theorem i1_cttz_true_refines_zero (x : LLVM.Int 1) :
    LLVM.Int.cttz x true ⊒ (.val (BitVec.ofInt 1 0)) := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val x =>
    rcases BitVec.eq_zero_or_eq_one x with rfl | rfl <;>
      simp [LLVM.Int.cttz, Id.run, pure, isRefinedBy, BitVec.ctz] <;> decide

public theorem allOnes_sub_eq_not (w : Nat) (x : LLVM.Int w) :
    LLVM.Int.sub (.val (BitVec.ofInt w (-1))) x =
      LLVM.Int.xor x (.val (BitVec.ofInt w (-1))) := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.xor, Id.run]
  | val x =>
    simp [LLVM.Int.sub, LLVM.Int.xor, Id.run]
    rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
      rw [BitVec.ofInt_neg]
      exact BitVec.neg_one_eq_allOnes]
    rw [BitVec.allOnes_sub_eq_not, BitVec.xor_allOnes]

public theorem allOnes_sub_refines_not (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w (-1))) x nsw nuw ⊒
      LLVM.Int.xor x (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans
    (sub_flags_refine w (.val (BitVec.ofInt w (-1))) x nsw nuw)
  rw [allOnes_sub_eq_not]
  exact isRefinedBy_refl _

public theorem add_refine_mono (w : Nat) {a a' b b' : LLVM.Int w}
    (ha : a ⊒ a') (hb : b ⊒ b') : LLVM.Int.add a b ⊒ LLVM.Int.add a' b' := by
  cases a with
  | poison => exact poison_isRefinedBy _
  | val a =>
    cases a' with
    | poison => simp [isRefinedBy] at ha
    | val a' =>
      have haa : a = a' := ha
      subst a'
      cases b with
      | poison => exact poison_isRefinedBy _
      | val b =>
        cases b' with
        | poison => simp [isRefinedBy] at hb
        | val b' =>
          have hbb : b = b' := hb
          subst b'
          exact isRefinedBy_refl _

public theorem sub_refine_mono (w : Nat) {a a' b b' : LLVM.Int w}
    (ha : a ⊒ a') (hb : b ⊒ b') : LLVM.Int.sub a b ⊒ LLVM.Int.sub a' b' := by
  cases a with
  | poison => exact poison_isRefinedBy _
  | val a =>
    cases a' with
    | poison => simp [isRefinedBy] at ha
    | val a' =>
      have haa : a = a' := ha
      subst a'
      cases b with
      | poison => exact poison_isRefinedBy _
      | val b =>
        cases b' with
        | poison => simp [isRefinedBy] at hb
        | val b' =>
          have hbb : b = b' := hb
          subst b'
          exact isRefinedBy_refl _

public theorem mul_refine_mono (w : Nat) {a a' b b' : LLVM.Int w}
    (ha : a ⊒ a') (hb : b ⊒ b') : LLVM.Int.mul a b ⊒ LLVM.Int.mul a' b' := by
  cases a with
  | poison => exact poison_isRefinedBy _
  | val a =>
    cases a' with
    | poison => simp [isRefinedBy] at ha
    | val a' =>
      have haa : a = a' := ha
      subst a'
      cases b with
      | poison => exact poison_isRefinedBy _
      | val b =>
        cases b' with
        | poison => simp [isRefinedBy] at hb
        | val b' =>
          have hbb : b = b' := hb
          subst b'
          exact isRefinedBy_refl _

public theorem mul_neg_neg (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.mul
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x)
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) y) =
      LLVM.Int.mul x y := by
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.mul, Id.run]

public theorem mul_neg_neg_flags_refine (w : Nat) (x y : LLVM.Int w)
    (negXNsw negXNuw negYNsw negYNuw mulNsw mulNuw : Bool) :
    LLVM.Int.mul
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x negXNsw negXNuw)
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) y negYNsw negYNuw)
        mulNsw mulNuw ⊒ LLVM.Int.mul x y := by
  apply isRefinedBy_trans (mul_flags_refine w _ _ mulNsw mulNuw)
  apply isRefinedBy_trans (mul_refine_mono w
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) x negXNsw negXNuw)
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) y negYNsw negYNuw))
  rw [mul_neg_neg]
  exact isRefinedBy_refl _

public theorem mul_neg_left (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.mul (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x) y =
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.mul x y) := by
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.mul, Id.run]

public theorem mul_neg_left_flags_refine (w : Nat) (x y : LLVM.Int w)
    (negNsw negNuw mulNsw mulNuw : Bool) :
    LLVM.Int.mul (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x negNsw negNuw)
        y mulNsw mulNuw ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.mul x y) := by
  apply isRefinedBy_trans (mul_flags_refine w _ _ mulNsw mulNuw)
  apply isRefinedBy_trans (mul_refine_mono w
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) x negNsw negNuw)
    (isRefinedBy_refl y))
  rw [mul_neg_left]
  exact isRefinedBy_refl _

public theorem mul_neg_right_flags_refine (w : Nat) (x y : LLVM.Int w)
    (negNsw negNuw mulNsw mulNuw : Bool) :
    LLVM.Int.mul x (LLVM.Int.sub (.val (BitVec.ofInt w 0)) y negNsw negNuw)
        mulNsw mulNuw ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.mul y x) := by
  rw [LLVM.Int.mul_comm]
  exact mul_neg_left_flags_refine w y x negNsw negNuw mulNsw mulNuw

public theorem mul_neg_constant_flags_refine (w : Nat) (x : LLVM.Int w)
    (c : BitVec w) (negNsw negNuw mulNsw mulNuw : Bool) :
    LLVM.Int.mul (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x negNsw negNuw)
        (.val c) mulNsw mulNuw ⊒ LLVM.Int.mul x (.val (-c)) := by
  apply isRefinedBy_trans (mul_flags_refine w _ _ mulNsw mulNuw)
  apply isRefinedBy_trans (mul_refine_mono w
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) x negNsw negNuw)
    (isRefinedBy_refl _))
  cases x <;> simp [LLVM.Int.sub, LLVM.Int.mul, Id.run]

public theorem add_neg_neg (w : Nat) (a b : LLVM.Int w) :
    LLVM.Int.add
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a)
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) b) =
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.add a b) := by
  cases a <;> cases b <;> simp [LLVM.Int.sub, LLVM.Int.add, Id.run]
  rw [BitVec.neg_add, BitVec.sub_eq_add_neg]

public theorem add_neg_left (w : Nat) (a b : LLVM.Int w) :
    LLVM.Int.add (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a) b =
      LLVM.Int.sub b a := by
  cases a <;> cases b <;> simp [LLVM.Int.sub, LLVM.Int.add, Id.run]
  rw [BitVec.sub_eq_add_neg, BitVec.add_comm]

public theorem add_neg_right (w : Nat) (a b : LLVM.Int w) :
    LLVM.Int.add a (LLVM.Int.sub (.val (BitVec.ofInt w 0)) b) =
      LLVM.Int.sub a b := by
  cases a <;> cases b <;> simp [LLVM.Int.sub, LLVM.Int.add, Id.run]
  rw [BitVec.add_neg_eq_sub]

public theorem sub_neg_right (w : Nat) (x a : LLVM.Int w) :
    LLVM.Int.sub x (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a) =
      LLVM.Int.add x a := by
  cases x <;> cases a <;> simp [LLVM.Int.sub, LLVM.Int.add, Id.run]

public theorem sub_add_self_refines_neg (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.sub x (LLVM.Int.add x y) ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) y := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val x =>
    cases y with
    | poison => exact isRefinedBy_refl _
    | val y =>
      simp [LLVM.Int.sub, LLVM.Int.add, Id.run, BitVec.sub_eq_add_neg,
        BitVec.neg_add]
      rw [← BitVec.add_assoc, BitVec.add_right_neg]
      simp

public theorem sub_add_self_commuted_refines_neg (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.sub x (LLVM.Int.add y x) ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) y := by
  rw [LLVM.Int.add_comm]
  exact sub_add_self_refines_neg w x y

public theorem sub_self_from_sub_refines_neg (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.sub (LLVM.Int.sub x y) x ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) y := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val x =>
    cases y with
    | poison => exact isRefinedBy_refl _
    | val y =>
      simp [LLVM.Int.sub, Id.run, BitVec.sub_eq_add_neg]
      rw [BitVec.add_comm x (-y), BitVec.add_assoc, BitVec.add_right_neg]
      simp

public theorem add_neg_neg_refines (w : Nat) (a b : LLVM.Int w)
    (negANsw negANuw negBNsw negBNuw addNsw addNuw : Bool) :
    LLVM.Int.add
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a negANsw negANuw)
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) b negBNsw negBNuw)
        addNsw addNuw ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.add a b) := by
  apply isRefinedBy_trans (add_flags_refine w _ _ addNsw addNuw)
  apply isRefinedBy_trans (add_refine_mono w
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) a negANsw negANuw)
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) b negBNsw negBNuw))
  rw [add_neg_neg]
  exact isRefinedBy_refl _

public theorem add_neg_left_refines (w : Nat) (a b : LLVM.Int w)
    (negNsw negNuw addNsw addNuw : Bool) :
    LLVM.Int.add (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a negNsw negNuw) b
        addNsw addNuw ⊒ LLVM.Int.sub b a := by
  apply isRefinedBy_trans (add_flags_refine w _ _ addNsw addNuw)
  apply isRefinedBy_trans (add_refine_mono w
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) a negNsw negNuw)
    (isRefinedBy_refl b))
  rw [add_neg_left]
  exact isRefinedBy_refl _

public theorem add_neg_right_refines (w : Nat) (a b : LLVM.Int w)
    (negNsw negNuw addNsw addNuw : Bool) :
    LLVM.Int.add a (LLVM.Int.sub (.val (BitVec.ofInt w 0)) b negNsw negNuw)
        addNsw addNuw ⊒ LLVM.Int.sub a b := by
  apply isRefinedBy_trans (add_flags_refine w _ _ addNsw addNuw)
  apply isRefinedBy_trans (add_refine_mono w (isRefinedBy_refl a)
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) b negNsw negNuw))
  rw [add_neg_right]
  exact isRefinedBy_refl _

public theorem sub_neg_right_refines (w : Nat) (x a : LLVM.Int w)
    (negNsw negNuw subNsw subNuw : Bool) :
    LLVM.Int.sub x (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a negNsw negNuw)
        subNsw subNuw ⊒ LLVM.Int.add x a := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ subNsw subNuw)
  apply isRefinedBy_trans (sub_refine_mono w (isRefinedBy_refl x)
    (sub_flags_refine w (.val (BitVec.ofInt w 0)) a negNsw negNuw))
  rw [sub_neg_right]
  exact isRefinedBy_refl _

public theorem sub_add_self_flags_refine_neg (w : Nat) (x y : LLVM.Int w)
    (addNsw addNuw subNsw subNuw : Bool) :
    LLVM.Int.sub x (LLVM.Int.add x y addNsw addNuw) subNsw subNuw ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) y := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ subNsw subNuw)
  apply isRefinedBy_trans (sub_refine_mono w (isRefinedBy_refl x)
    (add_flags_refine w x y addNsw addNuw))
  exact sub_add_self_refines_neg w x y

public theorem sub_add_self_commuted_flags_refine_neg (w : Nat) (x y : LLVM.Int w)
    (addNsw addNuw subNsw subNuw : Bool) :
    LLVM.Int.sub x (LLVM.Int.add y x addNsw addNuw) subNsw subNuw ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) y := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ subNsw subNuw)
  apply isRefinedBy_trans (sub_refine_mono w (isRefinedBy_refl x)
    (add_flags_refine w y x addNsw addNuw))
  exact sub_add_self_commuted_refines_neg w x y

public theorem sub_self_from_sub_flags_refine_neg (w : Nat) (x y : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.sub (LLVM.Int.sub x y innerNsw innerNuw) x outerNsw outerNuw ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) y := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ outerNsw outerNuw)
  apply isRefinedBy_trans (sub_refine_mono w
    (sub_flags_refine w x y innerNsw innerNuw) (isRefinedBy_refl x))
  exact sub_self_from_sub_refines_neg w x y

public theorem neg_constant (w : Nat) (value : Int) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0)) (.val (BitVec.ofInt w value)) =
      .val (BitVec.ofInt w (-value)) := by
  simp [LLVM.Int.sub, Id.run, pure]
  rw [BitVec.ofInt_neg]

public theorem neg_refine_mono (w : Nat) {x y : LLVM.Int w} (h : x ⊒ y) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0)) x ⊒
      LLVM.Int.sub (.val (BitVec.ofInt w 0)) y := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val x =>
    cases y with
    | poison => simp [isRefinedBy] at h
    | val y =>
      have hxy : x = y := h
      subst y
      exact isRefinedBy_refl _

public theorem trunc_flags_refine (w₁ w₂ : Nat) (h : w₂ < w₁) (x : LLVM.Int w₁)
    (nsw nuw : Bool) :
    LLVM.Int.trunc x w₂ nsw nuw h ⊒ LLVM.Int.trunc x w₂ false false h := by
  cases x with
  | poison => simp [LLVM.Int.trunc, isRefinedBy, Id.run]
  | val x =>
    by_cases hs : (x.truncate w₂).signExtend w₁ ≠ x
    <;> by_cases hu : (x.truncate w₂).zeroExtend w₁ ≠ x
    <;> cases nsw <;> cases nuw
    <;> simp [LLVM.Int.trunc, hs, hu, isRefinedBy, Id.run, pure]

public theorem trunc_refine_mono (w₁ w₂ : Nat) (h : w₂ < w₁)
    {x y : LLVM.Int w₁} (hxy : x ⊒ y) :
    LLVM.Int.trunc x w₂ false false h ⊒ LLVM.Int.trunc y w₂ false false h := by
  cases x with
  | poison => exact poison_isRefinedBy _
  | val x =>
    cases y with
    | poison => simp [isRefinedBy] at hxy
    | val y =>
      have hxy' : x = y := hxy
      subst y
      exact isRefinedBy_refl _

public theorem neg_trunc_neg (w₁ w₂ : Nat) (h : w₂ < w₁) (x : LLVM.Int w₁) :
    LLVM.Int.sub (.val (BitVec.ofInt w₂ 0))
        (LLVM.Int.trunc (LLVM.Int.sub (.val (BitVec.ofInt w₁ 0)) x)
          w₂ false false h) =
      LLVM.Int.trunc x w₂ false false h := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.trunc, Id.run]
  | val x =>
    simp [LLVM.Int.sub, LLVM.Int.trunc, Id.run]
    rw [BitVec.setWidth_neg_of_le (Nat.le_of_lt h)]
    simp

public theorem neg_trunc (w₁ w₂ : Nat) (h : w₂ < w₁) (x : LLVM.Int w₁) :
    LLVM.Int.sub (.val (BitVec.ofInt w₂ 0))
        (LLVM.Int.trunc x w₂ false false h) =
      LLVM.Int.trunc (LLVM.Int.sub (.val (BitVec.ofInt w₁ 0)) x)
        w₂ false false h := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.trunc, Id.run]
  | val x =>
    simp [LLVM.Int.sub, LLVM.Int.trunc, Id.run]
    rw [BitVec.setWidth_neg_of_le (Nat.le_of_lt h)]

public theorem neg_trunc_refines (w₁ w₂ : Nat) (h : w₂ < w₁) (x : LLVM.Int w₁)
    (truncNsw truncNuw outerNsw outerNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w₂ 0))
        (LLVM.Int.trunc x w₂ truncNsw truncNuw h) outerNsw outerNuw ⊒
      LLVM.Int.trunc (LLVM.Int.sub (.val (BitVec.ofInt w₁ 0)) x)
        w₂ false false h := by
  apply isRefinedBy_trans
    (sub_flags_refine w₂ (.val (BitVec.ofInt w₂ 0))
      (LLVM.Int.trunc x w₂ truncNsw truncNuw h) outerNsw outerNuw)
  apply isRefinedBy_trans
    (neg_refine_mono w₂ (trunc_flags_refine w₁ w₂ h x truncNsw truncNuw))
  rw [neg_trunc]
  exact isRefinedBy_refl _

public theorem neg_trunc_neg_refines (w₁ w₂ : Nat) (h : w₂ < w₁) (x : LLVM.Int w₁)
    (innerNsw innerNuw truncNsw truncNuw outerNsw outerNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w₂ 0))
        (LLVM.Int.trunc
          (LLVM.Int.sub (.val (BitVec.ofInt w₁ 0)) x innerNsw innerNuw)
          w₂ truncNsw truncNuw h)
        outerNsw outerNuw ⊒
      LLVM.Int.trunc x w₂ false false h := by
  apply isRefinedBy_trans
    (sub_flags_refine w₂ (.val (BitVec.ofInt w₂ 0))
      (LLVM.Int.trunc
        (LLVM.Int.sub (.val (BitVec.ofInt w₁ 0)) x innerNsw innerNuw)
        w₂ truncNsw truncNuw h)
      outerNsw outerNuw)
  apply isRefinedBy_trans (neg_refine_mono w₂
    (trunc_flags_refine w₁ w₂ h
      (LLVM.Int.sub (.val (BitVec.ofInt w₁ 0)) x innerNsw innerNuw)
      truncNsw truncNuw))
  apply isRefinedBy_trans (neg_refine_mono w₂
    (trunc_refine_mono w₁ w₂ h
      (sub_flags_refine w₁ (.val (BitVec.ofInt w₁ 0)) x innerNsw innerNuw)))
  rw [neg_trunc_neg]
  exact isRefinedBy_refl _

public theorem neg_increment_refines (w : Nat) (x : LLVM.Int w)
    (addNsw addNuw negNsw negNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.add x (.val (BitVec.ofInt w 1)) addNsw addNuw)
        negNsw negNuw ⊒
      LLVM.Int.xor x (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans
    (sub_flags_refine w (.val (BitVec.ofInt w 0))
      (LLVM.Int.add x (.val (BitVec.ofInt w 1)) addNsw addNuw) negNsw negNuw)
  apply isRefinedBy_trans (neg_refine_mono w
    (add_flags_refine w x (.val (BitVec.ofInt w 1)) addNsw addNuw))
  rw [neg_increment]
  exact isRefinedBy_refl _

public theorem neg_increment_commuted_refines (w : Nat) (x : LLVM.Int w)
    (addNsw addNuw negNsw negNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.add (.val (BitVec.ofInt w 1)) x addNsw addNuw)
        negNsw negNuw ⊒
      LLVM.Int.xor x (.val (BitVec.ofInt w (-1))) := by
  apply isRefinedBy_trans
    (sub_flags_refine w (.val (BitVec.ofInt w 0))
      (LLVM.Int.add (.val (BitVec.ofInt w 1)) x addNsw addNuw) negNsw negNuw)
  apply isRefinedBy_trans (neg_refine_mono w
    (add_flags_refine w (.val (BitVec.ofInt w 1)) x addNsw addNuw))
  rw [LLVM.Int.add_comm, neg_increment]
  exact isRefinedBy_refl _

public theorem neg_not (w : Nat) (x : LLVM.Int w) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) =
      LLVM.Int.add x (.val (BitVec.ofInt w 1)) := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run]
  | val x =>
    simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run, pure]
    rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
      rw [BitVec.ofInt_neg]
      exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
    rw [BitVec.neg_eq_not_add, BitVec.not_not]

public theorem neg_not_refines (w : Nat) (x : LLVM.Int w) (negNsw negNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) negNsw negNuw ⊒
      LLVM.Int.add x (.val (BitVec.ofInt w 1)) := by
  apply isRefinedBy_trans
    (sub_flags_refine w (.val (BitVec.ofInt w 0))
      (LLVM.Int.xor x (.val (BitVec.ofInt w (-1)))) negNsw negNuw)
  rw [neg_not]
  exact isRefinedBy_refl _

public theorem neg_sub (w : Nat) (a b : LLVM.Int w) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0)) (LLVM.Int.sub a b) = LLVM.Int.sub b a := by
  cases a <;> cases b <;> simp [LLVM.Int.sub, Id.run, pure]
  rw [BitVec.neg_sub, BitVec.sub_eq_add_neg, BitVec.add_comm]

public theorem neg_sub_refines (w : Nat) (a b : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.sub a b innerNsw innerNuw) outerNsw outerNuw ⊒
      LLVM.Int.sub b a := by
  apply isRefinedBy_trans
    (sub_flags_refine w (.val (BitVec.ofInt w 0))
      (LLVM.Int.sub a b innerNsw innerNuw) outerNsw outerNuw)
  apply isRefinedBy_trans (neg_refine_mono w (sub_flags_refine w a b innerNsw innerNuw))
  rw [neg_sub]
  exact isRefinedBy_refl _

theorem ssubOverflow_swap_of_neg {w : Nat} (a b : BitVec w)
    (inner : ¬ BitVec.ssubOverflow a b)
    (outer : ¬ BitVec.ssubOverflow 0 (a - b)) :
    ¬ BitVec.ssubOverflow b a := by
  rcases w with _ | w
  · rw [BitVec.eq_nil a, BitVec.eq_nil b]
    decide
  · have heq := BitVec.toInt_sub_of_not_ssubOverflow inner
    simp only [BitVec.ssubOverflow, Nat.add_one_sub_one, ge_iff_le,
      Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_le, Int.not_lt] at inner outer ⊢
    have hz : (0 : BitVec (w + 1)).toInt = 0 := by simp
    omega

public theorem neg_sub_nsw_refines (w : Nat) (a b : LLVM.Int w)
    (innerNuw outerNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.sub a b true innerNuw) true outerNuw ⊒
      LLVM.Int.sub b a true false := by
  rw [show BitVec.ofInt w 0 = 0 by simp]
  cases a with
  | poison => simp [LLVM.Int.sub, isRefinedBy, Id.run]
  | val a =>
    cases b with
    | poison => simp [LLVM.Int.sub, isRefinedBy, Id.run]
    | val b =>
      by_cases hinner : BitVec.ssubOverflow a b = true
      · simp [LLVM.Int.sub, Id.run, hinner, isRefinedBy]
      by_cases hinnerU : innerNuw = true ∧ BitVec.usubOverflow a b = true
      · simp [LLVM.Int.sub, Id.run, hinner, hinnerU, isRefinedBy]
      by_cases houter : BitVec.ssubOverflow 0 (a - b) = true
      · have houterZ : BitVec.ssubOverflow (0#w) (a - b) = true := by simpa using houter
        simp [LLVM.Int.sub, Id.run, hinner, hinnerU, houterZ, isRefinedBy, pure]
      by_cases houterU : outerNuw = true ∧ BitVec.usubOverflow 0 (a - b) = true
      · have houterZ : ¬ BitVec.ssubOverflow (0#w) (a - b) = true := by simpa using houter
        have houterUZ : outerNuw = true ∧ BitVec.usubOverflow (0#w) (a - b) = true := by
          simpa using houterU
        simp [LLVM.Int.sub, Id.run, hinner, hinnerU, houterZ, houterUZ, isRefinedBy, pure]
      have hswap := ssubOverflow_swap_of_neg a b hinner houter
      have houterZ : ¬ BitVec.ssubOverflow (0#w) (a - b) = true := by simpa using houter
      have houterUZ : ¬ (outerNuw = true ∧ BitVec.usubOverflow (0#w) (a - b) = true) := by
        simpa using houterU
      have heq : -(a - b) = b - a := by
        rw [BitVec.neg_sub]
        simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
      simp [LLVM.Int.sub, Id.run, hinner, hinnerU, houterZ, houterUZ, hswap,
        isRefinedBy, heq, pure]

public theorem neg_i1_refines (x : LLVM.Int 1) (nsw nuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt 1 0)) x nsw nuw ⊒ x := by
  apply isRefinedBy_trans (sub_flags_refine 1 (.val (BitVec.ofInt 1 0)) x nsw nuw)
  cases x with
  | poison => simp [LLVM.Int.sub, isRefinedBy, Id.run]
  | val x =>
    change LLVM.Int.sub (.val (BitVec.ofInt 1 0)) (.val x) ⊒ .val x
    simp [LLVM.Int.sub, isRefinedBy, Id.run]

public theorem double_neg_refines (w : Nat) (x : LLVM.Int w)
    (innerNsw innerNuw outerNsw outerNuw : Bool) :
    LLVM.Int.sub (.val (BitVec.ofInt w 0))
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x innerNsw innerNuw)
        outerNsw outerNuw ⊒ x := by
  cases x with
  | poison => simp [LLVM.Int.sub, isRefinedBy, Id.run]
  | val x =>
    have hz : BitVec.ofInt w 0 = 0 := by simp
    rw [hz]
    by_cases hs : innerNsw = true ∧ (0#w).ssubOverflow x = true
    · simp [LLVM.Int.sub, hs, isRefinedBy, Id.run]
    by_cases hu : innerNuw = true ∧ (0#w).usubOverflow x = true
    · simp [LLVM.Int.sub, hs, hu, isRefinedBy, Id.run]
    have hinner : LLVM.Int.sub (.val 0) (.val x) innerNsw innerNuw = .val (-x) := by
      simp [LLVM.Int.sub, hs, hu, Id.run]
    rw [hinner]
    simp only [LLVM.Int.sub, Id.run, pure]
    split
    · simp [isRefinedBy]
    · split <;> simp [isRefinedBy]

private theorem nat_add_eq_or_add_and (x y : Nat) :
    x + y = (x ||| y) + (x &&& y) := by
  induction y using Nat.div2Induction generalizing x with
  | ind y ih =>
    by_cases hy : y = 0
    · simp [hy]
    have hypos : 0 < y := Nat.pos_of_ne_zero hy
    have hrec := ih hypos (x / 2)
    have hxdec := Nat.div_add_mod x 2
    have hydec := Nat.div_add_mod y 2
    have hordec := Nat.div_add_mod (x ||| y) 2
    have handdec := Nat.div_add_mod (x &&& y) 2
    rw [Nat.or_div_two] at hordec
    rw [Nat.and_div_two] at handdec
    rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy' | hy'
    all_goals
      have horbit := Nat.testBit_or x y 0
      have handbit := Nat.testBit_and x y 0
      simp only [Nat.testBit_zero, hx, hy'] at horbit handbit
      rcases Nat.mod_two_eq_zero_or_one (x ||| y) with hor | hor <;>
        rcases Nat.mod_two_eq_zero_or_one (x &&& y) with hand | hand
      all_goals simp [hor, hand] at horbit handbit
      all_goals simp only [hx, hy', hor, hand, Nat.add_zero] at hxdec hydec hordec handdec
      omega

public theorem bitvec_add_eq_or_add_and {w : Nat} (x y : BitVec w) :
    x + y = (x ||| y) + (x &&& y) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_or, BitVec.toNat_and]
  rw [nat_add_eq_or_add_and]

public theorem bitvec_xor_add_and_eq_or {w : Nat} (x y : BitVec w) :
    (x ^^^ y) + (x &&& y) = x ||| y := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · ext i
    simp only [BitVec.getElem_or, BitVec.getElem_xor, BitVec.getElem_and]
    cases x[i] <;> cases y[i] <;> decide
  · ext i
    simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_zero]
    cases x[i] <;> cases y[i] <;> decide

public theorem bitvec_or_sub_and_eq_xor {w : Nat} (x y : BitVec w) :
    (x ||| y) - (x &&& y) = x ^^^ y := by
  calc
    (x ||| y) - (x &&& y) = ((x ^^^ y) + (x &&& y)) - (x &&& y) := by
      rw [bitvec_xor_add_and_eq_or]
    _ = x ^^^ y := BitVec.add_sub_cancel _ _

public theorem bitvec_add_sub_or_eq_and {w : Nat} (x y : BitVec w) :
    (x + y) - (x ||| y) = x &&& y := by
  calc
    (x + y) - (x ||| y) = ((x ||| y) + (x &&& y)) - (x ||| y) := by
      rw [bitvec_add_eq_or_add_and]
    _ = x &&& y := by
      rw [BitVec.add_comm]
      exact BitVec.add_sub_cancel _ _

public theorem bitvec_add_sub_and_eq_or {w : Nat} (x y : BitVec w) :
    (x + y) - (x &&& y) = x ||| y := by
  calc
    (x + y) - (x &&& y) = ((x ||| y) + (x &&& y)) - (x &&& y) := by
      rw [bitvec_add_eq_or_add_and]
    _ = x ||| y := BitVec.add_sub_cancel _ _

public theorem bitvec_or_sub_xor_eq_and {w : Nat} (x y : BitVec w) :
    (x ||| y) - (x ^^^ y) = x &&& y := by
  calc
    (x ||| y) - (x ^^^ y) = ((x ^^^ y) + (x &&& y)) - (x ^^^ y) := by
      rw [bitvec_xor_add_and_eq_or]
    _ = x &&& y := by
      rw [BitVec.add_comm]
      exact BitVec.add_sub_cancel _ _

public theorem bitvec_sub_and_eq_and_not {w : Nat} (x y : BitVec w) :
    x - (x &&& y) = x &&& ~~~y := by
  have h : (x &&& ~~~y) + (x &&& y) = x := by
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · ext i
      simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
      cases x[i] <;> cases y[i] <;> decide
    · ext i
      simp only [BitVec.getElem_and, BitVec.getElem_not, BitVec.getElem_zero]
      cases x[i] <;> cases y[i] <;> decide
  calc
    x - (x &&& y) = ((x &&& ~~~y) + (x &&& y)) - (x &&& y) := by rw [h]
    _ = x &&& ~~~y := BitVec.add_sub_cancel _ _

public theorem or_flags_refine (w : Nat) (x y : LLVM.Int w) (disjoint : Bool) :
    LLVM.Int.or x y disjoint ⊒ LLVM.Int.or x y := by
  cases x with
  | poison => simp [LLVM.Int.or, isRefinedBy, Id.run]
  | val x =>
    cases y with
    | poison => simp [LLVM.Int.or, isRefinedBy, Id.run]
    | val y =>
      cases disjoint
      · simp [LLVM.Int.or, isRefinedBy, Id.run]
      · simp only [LLVM.Int.or, Id.run, Bool.true_eq, true_and]
        split <;> simp [pure, isRefinedBy]

public theorem llvm_and_comm {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.and x y = LLVM.Int.and y x := by
  cases x <;> cases y <;>
    simp [LLVM.Int.and, Id.run, BitVec.and_comm]

public theorem llvm_or_comm {w : Nat} (x y : LLVM.Int w) (disjoint : Bool) :
    LLVM.Int.or x y disjoint = LLVM.Int.or y x disjoint := by
  cases x <;> cases y <;>
    simp [LLVM.Int.or, Id.run, BitVec.and_comm, BitVec.or_comm]

public theorem llvm_xor_comm {w : Nat} (x y : LLVM.Int w) :
    LLVM.Int.xor x y = LLVM.Int.xor y x := by
  cases x <;> cases y <;>
    simp [LLVM.Int.xor, Id.run, BitVec.xor_comm]

public theorem xor_refine_mono (w : Nat) {a a' b b' : LLVM.Int w}
    (ha : a ⊒ a') (hb : b ⊒ b') : LLVM.Int.xor a b ⊒ LLVM.Int.xor a' b' := by
  cases a with
  | poison => exact poison_isRefinedBy _
  | val a =>
    cases a' with
    | poison => simp [isRefinedBy] at ha
    | val a' =>
      have haa : a = a' := ha
      subst a'
      cases b with
      | poison => exact poison_isRefinedBy _
      | val b =>
        cases b' with
        | poison => simp [isRefinedBy] at hb
        | val b' =>
          have hbb : b = b' := hb
          subst b'
          exact isRefinedBy_refl _

public theorem bitvec_and_xor_or_eq_xor {w : Nat} (x y : BitVec w) :
    (x &&& y) ^^^ (x ||| y) = x ^^^ y := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> decide

public theorem xor_and_or_refines_xor (w : Nat) (x y : LLVM.Int w)
    (disjoint : Bool) :
    LLVM.Int.xor (LLVM.Int.and x y) (LLVM.Int.or x y disjoint) ⊒
      LLVM.Int.xor x y := by
  apply isRefinedBy_trans
    (xor_refine_mono w (isRefinedBy_refl _) (or_flags_refine w x y disjoint))
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run,
    bitvec_and_xor_or_eq_xor]

public theorem bitvec_and_xor_xor_eq_or {w : Nat} (x y : BitVec w) :
    (x &&& y) ^^^ (x ^^^ y) = x ||| y := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_or]
  cases x[i] <;> cases y[i] <;> decide

public theorem xor_and_xor_eq_or (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.and x y) (LLVM.Int.xor x y) = LLVM.Int.or x y := by
  cases x <;> cases y <;> simp [LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or, Id.run,
    bitvec_and_xor_xor_eq_or]

public theorem xor_and_xor_refines_or (w : Nat) (x y : LLVM.Int w) :
    LLVM.Int.xor (LLVM.Int.and x y) (LLVM.Int.xor x y) ⊒ LLVM.Int.or x y := by
  rw [xor_and_xor_eq_or]
  exact isRefinedBy_refl _

public theorem add_and_xor_refines_or (w : Nat) (x y : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.add (LLVM.Int.and x y) (LLVM.Int.xor x y) nsw nuw ⊒
      LLVM.Int.or x y := by
  apply isRefinedBy_trans (add_flags_refine w _ _ nsw nuw)
  rw [LLVM.Int.add_comm]
  cases x <;> cases y <;> simp [LLVM.Int.add, LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or,
    Id.run, bitvec_xor_add_and_eq_or]

public theorem add_xor_and_refines_or (w : Nat) (x y : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.add (LLVM.Int.xor x y) (LLVM.Int.and x y) nsw nuw ⊒
      LLVM.Int.or x y := by
  apply isRefinedBy_trans (add_flags_refine w _ _ nsw nuw)
  cases x <;> cases y <;> simp [LLVM.Int.add, LLVM.Int.xor, LLVM.Int.and, LLVM.Int.or,
    Id.run, bitvec_xor_add_and_eq_or]

public theorem sub_or_and_refines_xor (w : Nat) (x y : LLVM.Int w)
    (disjoint nsw nuw : Bool) :
    LLVM.Int.sub (LLVM.Int.or x y disjoint) (LLVM.Int.and x y) nsw nuw ⊒
      LLVM.Int.xor x y := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ nsw nuw)
  apply isRefinedBy_trans (sub_refine_mono w (or_flags_refine w x y disjoint)
    (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.or, LLVM.Int.and, LLVM.Int.xor,
    Id.run, bitvec_or_sub_and_eq_xor]

public theorem sub_add_or_refines_and (w : Nat) (x y : LLVM.Int w)
    (addNsw addNuw disjoint subNsw subNuw : Bool) :
    LLVM.Int.sub (LLVM.Int.add x y addNsw addNuw) (LLVM.Int.or x y disjoint)
        subNsw subNuw ⊒ LLVM.Int.and x y := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ subNsw subNuw)
  apply isRefinedBy_trans (sub_refine_mono w (add_flags_refine w x y addNsw addNuw)
    (or_flags_refine w x y disjoint))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.or, LLVM.Int.and,
    Id.run, bitvec_add_sub_or_eq_and]

public theorem sub_add_and_refines_or (w : Nat) (x y : LLVM.Int w)
    (addNsw addNuw subNsw subNuw : Bool) :
    LLVM.Int.sub (LLVM.Int.add x y addNsw addNuw) (LLVM.Int.and x y)
        subNsw subNuw ⊒ LLVM.Int.or x y := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ subNsw subNuw)
  apply isRefinedBy_trans (sub_refine_mono w (add_flags_refine w x y addNsw addNuw)
    (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.or, LLVM.Int.and,
    Id.run, bitvec_add_sub_and_eq_or]

public theorem sub_or_xor_refines_and (w : Nat) (x y : LLVM.Int w)
    (disjoint nsw nuw : Bool) :
    LLVM.Int.sub (LLVM.Int.or x y disjoint) (LLVM.Int.xor x y) nsw nuw ⊒
      LLVM.Int.and x y := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ nsw nuw)
  apply isRefinedBy_trans (sub_refine_mono w (or_flags_refine w x y disjoint)
    (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.or, LLVM.Int.xor, LLVM.Int.and,
    Id.run, bitvec_or_sub_xor_eq_and]

public theorem sub_and_refines_and_not (w : Nat) (x y : LLVM.Int w)
    (nsw nuw : Bool) :
    LLVM.Int.sub x (LLVM.Int.and x y) nsw nuw ⊒
      LLVM.Int.and x (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) := by
  apply isRefinedBy_trans (sub_flags_refine w _ _ nsw nuw)
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.and, LLVM.Int.xor, Id.run]
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes, BitVec.xor_allOnes]
  rw [bitvec_sub_and_eq_and_not]
  exact isRefinedBy_refl _

public theorem bitvec_sub_add_allones_eq_not_add {w : Nat} (x y : BitVec w) :
    (x - y) + BitVec.ofInt w (-1) = (y ^^^ BitVec.ofInt w (-1)) + x := by
  rw [show BitVec.ofInt w (-1) = BitVec.allOnes w by
    rw [BitVec.ofInt_neg]
    exact BitVec.neg_one_eq_allOnes]
  rw [BitVec.xor_allOnes, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add]
  rw [BitVec.add_assoc, BitVec.add_assoc]
  rw [show (1#w) + BitVec.allOnes w = 0#w by
    rw [← BitVec.neg_one_eq_allOnes]
    rw [← BitVec.sub_eq_add_neg]
    exact BitVec.sub_self _]
  rw [BitVec.add_zero, BitVec.add_comm]

public theorem add_sub_allones_refines_not_add (w : Nat) (x y : LLVM.Int w)
    (subNsw subNuw addNsw addNuw : Bool) :
    LLVM.Int.add (LLVM.Int.sub x y subNsw subNuw)
        (.val (BitVec.ofInt w (-1))) addNsw addNuw ⊒
      LLVM.Int.add (LLVM.Int.xor y (.val (BitVec.ofInt w (-1)))) x := by
  apply isRefinedBy_trans (add_flags_refine w _ _ addNsw addNuw)
  apply isRefinedBy_trans (add_refine_mono w
    (sub_flags_refine w x y subNsw subNuw) (isRefinedBy_refl _))
  cases x <;> cases y <;> simp [LLVM.Int.sub, LLVM.Int.add, LLVM.Int.xor, Id.run,
    bitvec_sub_add_allones_eq_not_add]

public theorem bitvec_add_sub_constants {w : Nat} (x c1 c2 : BitVec w) :
    (c1 - x) + c2 = (c1 + c2) - x := by
  rw [BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg]
  rw [BitVec.add_assoc, BitVec.add_comm (-x) c2, ← BitVec.add_assoc]

public theorem add_sub_constants_refine (w : Nat) (x : LLVM.Int w) (c1 c2 : BitVec w)
    (subNsw subNuw addNsw addNuw : Bool) :
    LLVM.Int.add (LLVM.Int.sub (.val c1) x subNsw subNuw) (.val c2) addNsw addNuw ⊒
      LLVM.Int.sub (.val (c1 + c2)) x := by
  apply isRefinedBy_trans (add_flags_refine w _ _ addNsw addNuw)
  apply isRefinedBy_trans (add_refine_mono w
    (sub_flags_refine w (.val c1) x subNsw subNuw) (isRefinedBy_refl _))
  cases x <;> simp [LLVM.Int.sub, LLVM.Int.add, Id.run, bitvec_add_sub_constants]

theorem subNegConstantOverflow {w : Nat} (x c : BitVec w)
    (hc : c ≠ BitVec.intMin w)
    (hsub : ¬ BitVec.ssubOverflow x c = true) :
    ¬ BitVec.saddOverflow x (-c) = true := by
  rcases w with _ | w
  · rw [BitVec.eq_nil c] at hc
    exact (hc (BitVec.eq_nil _)).elim
  · have hcneg := BitVec.toInt_neg_of_ne_intMin hc
    simp only [BitVec.ssubOverflow, BitVec.saddOverflow, Nat.add_one_sub_one,
      ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or,
      Int.not_le, Int.not_lt] at hsub ⊢
    rw [hcneg]
    omega

/-- Folding a scalar constant RHS through `x - c -> x + (-c)`, clearing flags. -/
public theorem sub_neg_constant_refines (w : Nat) (x : LLVM.Int w) (c : BitVec w)
    (nsw nuw : Bool) :
    LLVM.Int.sub x (.val c) nsw nuw ⊒ LLVM.Int.add x (.val (-c)) := by
  apply isRefinedBy_trans (sub_flags_refine w x (.val c) nsw nuw)
  cases x <;> simp [LLVM.Int.sub, LLVM.Int.add, Id.run, BitVec.sub_eq_add_neg]

/-- Folding a non-signed-minimum scalar constant RHS while preserving `nsw`. -/
public theorem sub_neg_constant_nsw_refines (w : Nat) (x : LLVM.Int w) (c : BitVec w)
    (hc : c ≠ BitVec.intMin w) (nuw : Bool) :
    LLVM.Int.sub x (.val c) true nuw ⊒ LLVM.Int.add x (.val (-c)) true false := by
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.add, isRefinedBy, Id.run]
  | val x =>
    by_cases hsub : BitVec.ssubOverflow x c = true
    · simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hsub, isRefinedBy, pure]
    by_cases hsubU : nuw = true ∧ BitVec.usubOverflow x c = true
    · simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hsub, hsubU, isRefinedBy, pure]
    have htarget := subNegConstantOverflow x c hc hsub
    have heq : x - c = x + -c := by rw [BitVec.sub_eq_add_neg]
    simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hsub, hsubU, htarget, heq,
      isRefinedBy]

theorem addNegLeftOverflow {w : Nat} (a b : BitVec w)
    (hneg : ¬ BitVec.ssubOverflow 0 a = true)
    (hadd : ¬ BitVec.saddOverflow (-a) b = true) :
    ¬ BitVec.ssubOverflow b a = true := by
  rcases w with _ | w
  · rw [BitVec.eq_nil a, BitVec.eq_nil b]
    decide
  · have hnegEq := BitVec.toInt_sub_of_not_ssubOverflow hneg
    simp only [BitVec.ssubOverflow, BitVec.saddOverflow, Nat.add_one_sub_one,
      ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or,
      Int.not_le, Int.not_lt] at hneg hadd ⊢
    have hz : (0 : BitVec (w + 1)).toInt = 0 := by simp
    have hzeroSub : (0 : BitVec (w + 1)) - a = -a := by simp
    rw [hzeroSub, hz] at hnegEq
    omega

theorem addNegRightOverflow {w : Nat} (a b : BitVec w)
    (hneg : ¬ BitVec.ssubOverflow 0 b = true)
    (hadd : ¬ BitVec.saddOverflow a (-b) = true) :
    ¬ BitVec.ssubOverflow a b = true := by
  rcases w with _ | w
  · rw [BitVec.eq_nil a, BitVec.eq_nil b]
    decide
  · have hnegEq := BitVec.toInt_sub_of_not_ssubOverflow hneg
    simp only [BitVec.ssubOverflow, BitVec.saddOverflow, Nat.add_one_sub_one,
      ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or,
      Int.not_le, Int.not_lt] at hneg hadd ⊢
    have hz : (0 : BitVec (w + 1)).toInt = 0 := by simp
    have hzeroSub : (0 : BitVec (w + 1)) - b = -b := by simp
    rw [hzeroSub, hz] at hnegEq
    omega

theorem subNegRightOverflow {w : Nat} (x a : BitVec w)
    (hneg : ¬ BitVec.ssubOverflow 0 a = true)
    (hsub : ¬ BitVec.ssubOverflow x (-a) = true) :
    ¬ BitVec.saddOverflow x a = true := by
  rcases w with _ | w
  · rw [BitVec.eq_nil x, BitVec.eq_nil a]
    decide
  · have hnegEq := BitVec.toInt_sub_of_not_ssubOverflow hneg
    simp only [BitVec.ssubOverflow, BitVec.saddOverflow, Nat.add_one_sub_one,
      ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or,
      Int.not_le, Int.not_lt] at hneg hsub ⊢
    have hz : (0 : BitVec (w + 1)).toInt = 0 := by simp
    have hzeroSub : (0 : BitVec (w + 1)) - a = -a := by simp
    rw [hzeroSub, hz] at hnegEq
    omega

theorem mulNegNegOverflow {w : Nat} (x y : BitVec w)
    (hnegx : ¬ BitVec.ssubOverflow 0 x = true)
    (hnegy : ¬ BitVec.ssubOverflow 0 y = true)
    (hmul : ¬ BitVec.smulOverflow (-x) (-y) = true) :
    ¬ BitVec.smulOverflow x y = true := by
  rcases w with _ | w
  · rw [BitVec.eq_nil x, BitVec.eq_nil y]
    decide
  · have hnegxEq := BitVec.toInt_sub_of_not_ssubOverflow hnegx
    have hnegyEq := BitVec.toInt_sub_of_not_ssubOverflow hnegy
    simp only [BitVec.ssubOverflow, BitVec.smulOverflow, Nat.add_one_sub_one,
      ge_iff_le, Bool.or_eq_true, decide_eq_true_eq, not_or,
      Int.not_le, Int.not_lt] at hnegx hnegy hmul ⊢
    have hz : (0 : BitVec (w + 1)).toInt = 0 := by simp
    have hzeroSubX : (0 : BitVec (w + 1)) - x = -x := by simp
    have hzeroSubY : (0 : BitVec (w + 1)) - y = -y := by simp
    rw [hzeroSubX, hz] at hnegxEq
    rw [hzeroSubY, hz] at hnegyEq
    rw [hnegxEq, hnegyEq] at hmul
    simpa [Int.neg_mul_neg] using hmul

/-- Preserving `nsw` across `(-a) + b -> b - a` when both source operations are `nsw`. -/
public theorem add_neg_left_nsw_refines (w : Nat) (a b : LLVM.Int w)
    (negNuw addNuw : Bool) :
    LLVM.Int.add (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a true negNuw) b
        true addNuw ⊒ LLVM.Int.sub b a true false := by
  rw [show BitVec.ofInt w 0 = 0 by simp]
  cases a with
  | poison => simp [LLVM.Int.sub, LLVM.Int.add, isRefinedBy, Id.run]
  | val a =>
    cases b with
    | poison =>
      simp only [LLVM.Int.sub, LLVM.Int.add, Id.run, pure]
      split <;> simp [isRefinedBy]
    | val b =>
      by_cases hneg : BitVec.ssubOverflow 0 a = true
      · have hnegZ : BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, isRefinedBy, pure]
      by_cases hnegU : negNuw = true ∧ BitVec.usubOverflow 0 a = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        have hnegUZ : negNuw = true ∧ BitVec.usubOverflow (0#w) a = true := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, isRefinedBy, pure]
      by_cases hadd : BitVec.saddOverflow (-a) b = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) a = true) := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hadd,
          isRefinedBy, pure]
      by_cases haddU : addNuw = true ∧ BitVec.uaddOverflow (-a) b = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) a = true) := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hadd, haddU,
          isRefinedBy, pure]
      have htarget := addNegLeftOverflow a b hneg hadd
      have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
      have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) a = true) := by
        simpa using hnegU
      have heq : -a + b = b - a := by
        rw [BitVec.sub_eq_add_neg, BitVec.add_comm]
      simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hadd, haddU,
        htarget, heq, isRefinedBy]

/-- Preserving `nsw` across `a + (-b) -> a - b` when both source operations are `nsw`. -/
public theorem add_neg_right_nsw_refines (w : Nat) (a b : LLVM.Int w)
    (negNuw addNuw : Bool) :
    LLVM.Int.add a (LLVM.Int.sub (.val (BitVec.ofInt w 0)) b true negNuw)
        true addNuw ⊒ LLVM.Int.sub a b true false := by
  rw [show BitVec.ofInt w 0 = 0 by simp]
  cases a with
  | poison => simp [LLVM.Int.sub, LLVM.Int.add, isRefinedBy, Id.run]
  | val a =>
    cases b with
    | poison => simp [LLVM.Int.sub, LLVM.Int.add, isRefinedBy, Id.run]
    | val b =>
      by_cases hneg : BitVec.ssubOverflow 0 b = true
      · have hnegZ : BitVec.ssubOverflow (0#w) b = true := by simpa using hneg
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, isRefinedBy, pure]
      by_cases hnegU : negNuw = true ∧ BitVec.usubOverflow 0 b = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) b = true := by simpa using hneg
        have hnegUZ : negNuw = true ∧ BitVec.usubOverflow (0#w) b = true := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, isRefinedBy, pure]
      by_cases hadd : BitVec.saddOverflow a (-b) = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) b = true := by simpa using hneg
        have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) b = true) := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hadd,
          isRefinedBy, pure]
      by_cases haddU : addNuw = true ∧ BitVec.uaddOverflow a (-b) = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) b = true := by simpa using hneg
        have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) b = true) := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hadd, haddU,
          isRefinedBy, pure]
      have htarget := addNegRightOverflow a b hneg hadd
      have hnegZ : ¬ BitVec.ssubOverflow (0#w) b = true := by simpa using hneg
      have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) b = true) := by
        simpa using hnegU
      have heq : a + -b = a - b := by rw [BitVec.add_neg_eq_sub]
      simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hadd, haddU,
        htarget, heq, isRefinedBy]

/-- Preserving `nsw` across `x - (-a) -> x + a` when both source operations are `nsw`. -/
public theorem sub_neg_right_nsw_refines (w : Nat) (x a : LLVM.Int w)
    (negNuw subNuw : Bool) :
    LLVM.Int.sub x (LLVM.Int.sub (.val (BitVec.ofInt w 0)) a true negNuw)
        true subNuw ⊒ LLVM.Int.add x a true false := by
  rw [show BitVec.ofInt w 0 = 0 by simp]
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.add, isRefinedBy, Id.run]
  | val x =>
    cases a with
    | poison => simp [LLVM.Int.sub, LLVM.Int.add, isRefinedBy, Id.run]
    | val a =>
      by_cases hneg : BitVec.ssubOverflow 0 a = true
      · have hnegZ : BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, isRefinedBy, pure]
      by_cases hnegU : negNuw = true ∧ BitVec.usubOverflow 0 a = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        have hnegUZ : negNuw = true ∧ BitVec.usubOverflow (0#w) a = true := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, isRefinedBy, pure]
      by_cases hsub : BitVec.ssubOverflow x (-a) = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) a = true) := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hsub,
          isRefinedBy, pure]
      by_cases hsubU : subNuw = true ∧ BitVec.usubOverflow x (-a) = true
      · have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
        have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) a = true) := by
          simpa using hnegU
        simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hsub, hsubU,
          isRefinedBy, pure]
      have htarget := subNegRightOverflow x a hneg hsub
      have hnegZ : ¬ BitVec.ssubOverflow (0#w) a = true := by simpa using hneg
      have hnegUZ : ¬ (negNuw = true ∧ BitVec.usubOverflow (0#w) a = true) := by
        simpa using hnegU
      have heq : x - -a = x + a := by simp [BitVec.sub_eq_add_neg]
      simp [LLVM.Int.sub, LLVM.Int.add, Id.run, hnegZ, hnegUZ, hsub, hsubU,
        htarget, heq, isRefinedBy]

/-- Preserving `nsw` across `(-x) * (-y) -> x * y` when both negations and the
    source multiplication are `nsw`. -/
public theorem mul_neg_neg_nsw_refines (w : Nat) (x y : LLVM.Int w)
    (negXNuw negYNuw mulNuw : Bool) :
    LLVM.Int.mul
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) x true negXNuw)
        (LLVM.Int.sub (.val (BitVec.ofInt w 0)) y true negYNuw)
        true mulNuw ⊒ LLVM.Int.mul x y true false := by
  rw [show BitVec.ofInt w 0 = 0 by simp]
  cases x with
  | poison => simp [LLVM.Int.sub, LLVM.Int.mul, isRefinedBy, Id.run]
  | val x =>
    cases y with
    | poison =>
      simp only [LLVM.Int.sub, LLVM.Int.mul, Id.run, pure]
      split <;> simp [isRefinedBy]
    | val y =>
      by_cases hnegx : BitVec.ssubOverflow 0 x = true
      · have hnegxZ : BitVec.ssubOverflow (0#w) x = true := by simpa using hnegx
        simp [LLVM.Int.sub, LLVM.Int.mul, Id.run, hnegxZ, isRefinedBy, pure]
      by_cases hnegxU : negXNuw = true ∧ BitVec.usubOverflow 0 x = true
      · have hnegxZ : ¬ BitVec.ssubOverflow (0#w) x = true := by simpa using hnegx
        have hnegxUZ : negXNuw = true ∧ BitVec.usubOverflow (0#w) x = true := by
          simpa using hnegxU
        simp [LLVM.Int.sub, LLVM.Int.mul, Id.run, hnegxZ, hnegxUZ,
          isRefinedBy, pure]
      by_cases hnegy : BitVec.ssubOverflow 0 y = true
      · have hnegxZ : ¬ BitVec.ssubOverflow (0#w) x = true := by simpa using hnegx
        have hnegxUZ : ¬ (negXNuw = true ∧ BitVec.usubOverflow (0#w) x = true) := by
          simpa using hnegxU
        have hnegyZ : BitVec.ssubOverflow (0#w) y = true := by simpa using hnegy
        simp [LLVM.Int.sub, LLVM.Int.mul, Id.run, hnegxZ, hnegxUZ, hnegyZ,
          isRefinedBy, pure]
      by_cases hnegyU : negYNuw = true ∧ BitVec.usubOverflow 0 y = true
      · have hnegxZ : ¬ BitVec.ssubOverflow (0#w) x = true := by simpa using hnegx
        have hnegxUZ : ¬ (negXNuw = true ∧ BitVec.usubOverflow (0#w) x = true) := by
          simpa using hnegxU
        have hnegyZ : ¬ BitVec.ssubOverflow (0#w) y = true := by simpa using hnegy
        have hnegyUZ : negYNuw = true ∧ BitVec.usubOverflow (0#w) y = true := by
          simpa using hnegyU
        simp [LLVM.Int.sub, LLVM.Int.mul, Id.run, hnegxZ, hnegxUZ, hnegyZ,
          hnegyUZ, isRefinedBy, pure]
      by_cases hmul : BitVec.smulOverflow (-x) (-y) = true
      · have hnegxZ : ¬ BitVec.ssubOverflow (0#w) x = true := by simpa using hnegx
        have hnegxUZ : ¬ (negXNuw = true ∧ BitVec.usubOverflow (0#w) x = true) := by
          simpa using hnegxU
        have hnegyZ : ¬ BitVec.ssubOverflow (0#w) y = true := by simpa using hnegy
        have hnegyUZ : ¬ (negYNuw = true ∧ BitVec.usubOverflow (0#w) y = true) := by
          simpa using hnegyU
        simp [LLVM.Int.sub, LLVM.Int.mul, Id.run, hnegxZ, hnegxUZ, hnegyZ,
          hnegyUZ, hmul, isRefinedBy, pure]
      by_cases hmulU : mulNuw = true ∧ BitVec.umulOverflow (-x) (-y) = true
      · have hnegxZ : ¬ BitVec.ssubOverflow (0#w) x = true := by simpa using hnegx
        have hnegxUZ : ¬ (negXNuw = true ∧ BitVec.usubOverflow (0#w) x = true) := by
          simpa using hnegxU
        have hnegyZ : ¬ BitVec.ssubOverflow (0#w) y = true := by simpa using hnegy
        have hnegyUZ : ¬ (negYNuw = true ∧ BitVec.usubOverflow (0#w) y = true) := by
          simpa using hnegyU
        simp [LLVM.Int.sub, LLVM.Int.mul, Id.run, hnegxZ, hnegxUZ, hnegyZ,
          hnegyUZ, hmul, hmulU, isRefinedBy, pure]
      have htarget := mulNegNegOverflow x y hnegx hnegy hmul
      have hnegxZ : ¬ BitVec.ssubOverflow (0#w) x = true := by simpa using hnegx
      have hnegxUZ : ¬ (negXNuw = true ∧ BitVec.usubOverflow (0#w) x = true) := by
        simpa using hnegxU
      have hnegyZ : ¬ BitVec.ssubOverflow (0#w) y = true := by simpa using hnegy
      have hnegyUZ : ¬ (negYNuw = true ∧ BitVec.usubOverflow (0#w) y = true) := by
        simpa using hnegyU
      have heq : (-x) * (-y) = x * y := by simp
      simp [LLVM.Int.sub, LLVM.Int.mul, Id.run, hnegxZ, hnegxUZ, hnegyZ,
        hnegyUZ, hmul, hmulU, htarget, heq, isRefinedBy]

end Veir.Passes.InstCombineLLVM
