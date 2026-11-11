import Veir.PatternRewriter.Puddle.Builders
import Veir.PatternRewriter.Puddle.Execution
import Veir.PatternRewriter.Puddle.Validity
import Veir.PatternRewriter.Puddle.CTreeValidity
import Veir.Input
import Veir.Printer

open Veir
open Veir.Input
open Veir.Puddle
open Veir.Data

/-!
## Useful lemmas for reasoning about `InterpretsTo` and `RuntimeValue` refinements
-/

private theorem constant_iff (ty : IntegerType) (props : propertiesOf (.arith .constant : OpCode))
    (v : RuntimeValue) :
    InterpretsTo (.arith .constant) props #[ty] #[] #[v] ↔
      ∃ attr, props = .int attr ∧ v = .int ty.bitwidth (.val (BitVec.ofInt ty.bitwidth attr.value)) := by
  cases props <;> simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms, List.getElem!_toArray,
    List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, true_and, interpretOp', Arith.interpretOp', List.getElem_toArray,
    TypeAttr.of_val, Attribute.of, Interp.pure_eq, reduceCtorEq, false_and, exists_false]
  all_goals
    constructor
    · rintro ⟨_, h⟩
      grind [h .empty]
    · grind

private theorem addi_iff {signedness : IntegerType.Signedness} (w : Nat) (props : propertiesOf (.arith .addi : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .addi) props #[IntegerType.mk w signedness] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.add x y props.attr.nsw props.attr.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms, List.getElem!_toArray,
    List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, true_and, interpretOp', Arith.interpretOp', ne_eq, not_true_eq_false,
    ↓reduceDIte, LLVM.Int.cast_self, Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true]
  constructor
  · rintro ⟨_, h⟩
    grind [h .empty]
  · grind

private theorem muli_iff {signedness : IntegerType.Signedness} (w : Nat) (props : propertiesOf (.arith .muli : OpCode))
    (x y : LLVM.Int w) (v : RuntimeValue) :
    InterpretsTo (.arith .muli) props #[IntegerType.mk w signedness] #[.int w x, .int w y] #[v] ↔
      v = .int w (LLVM.Int.mul x y props.attr.nsw props.attr.nuw) := by
  simp only [InterpretsTo, RuntimeValue.ArrayConforms, List.size_toArray, List.length_cons,
    List.length_nil, Nat.zero_add, Nat.lt_one_iff, RuntimeValue.Conforms, List.getElem!_toArray,
    List.getElem!_eq_getElem?_getD, forall_eq, Nat.lt_add_one, getElem?_pos, List.getElem_cons_zero,
    Option.getD_some, true_and, interpretOp', Arith.interpretOp', ne_eq, not_true_eq_false,
    ↓reduceDIte, LLVM.Int.cast_self, Interp.pure_eq, Interp.bind_ok, Interp.ok.injEq, Prod.mk.injEq,
    Array.mk.injEq, List.cons.injEq, and_true, forall_const]
  grind

private theorem add_zero_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.add x (.val (BitVec.ofInt w 0)) nsw nuw) ⊒ .int w x := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.add, isRefinedBy, Id.run, pure]
  grind

private theorem mul_two_refines (w : Nat) (x : LLVM.Int w) (nsw nuw : Bool) :
    RuntimeValue.int w (LLVM.Int.mul x (.val (BitVec.ofInt w 2)) nsw nuw) ⊒
      .int w (LLVM.Int.add x x) := by
  cases x <;> simp [RuntimeValue.isRefinedBy, LLVM.Int.mul, LLVM.Int.add,
    isRefinedBy, Id.run, pure, BitVec.mul_two]
  grind

/- ## Example patterns -/

/-- Match an arithmetic constant of a given value. -/
def matchConstant (returnType : Handle OpCode .type) (constant : Int)
    : MatchProg.Builder (Handle OpCode .value) := do
  let op ← MatchProg.operation (.arith .constant) #[] #[returnType]
    (fun properties => properties.intAttr?.any (·.value = constant))
  return op.res[0]!

/-- Rewrite `x + 0` to `x`. -/
private def addZero : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 0
      let _ ← MatchProg.root (.arith .addi) #[x, cstVal] #[returnType]
      return x)
    pure
    (fun x => x)

theorem addZero_valid : Pattern.Valid addZero := by
  simp only [addZero, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val propzero _ hinterpCst
  obtain ⟨_, rfl, rfl⟩ := (constant_iff _ _ _).mp hinterpCst
  intro addProp val _ hinterpAdd
  obtain rfl := (addi_iff _ _ _ _ _).mp hinterpAdd
  grind [add_zero_refines]

/-- Rewrite `x * 2` to `x + x`. -/
private def mulTwo : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cstVal ← matchConstant returnType 2
      let _ ← MatchProg.root (.arith .muli) #[x, cstVal] #[returnType]
      return (returnType, x))
    (fun (returnType, x) => do
      let properties ← CreateProg.property (.arith .addi)
        (default : propertiesOf (.arith .addi : OpCode))
      let add ← CreateProg.operation (.arith .addi) #[x, x] #[returnType] properties
      return add)
    (fun result => result)

theorem mulTwo_valid : Pattern.Valid mulTwo := by
  simp only [mulTwo, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val proptwo _ hinterpCst
  obtain ⟨_, rfl, rfl⟩ := (constant_iff _ _ _).mp hinterpCst
  intro mulProp val _ hinterpMul
  obtain rfl := (muli_iff _ _ _ _ _).mp hinterpMul
  exists (.int w (LLVM.Int.add x x))
  constructor; exact (addi_iff _ _ _ _ _).mpr rfl
  grind [mul_two_refines]

/-- Rewrite `x + 0` to `x`, matching the zero with a native metadata predicate. -/
private def nativeMatch : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cst ← MatchProg.operation (.arith .constant) #[] #[returnType]
      MatchProg.matchNative (returnType, cst.properties)
        (fun (type, properties) =>
          type = (IntegerType.signless 32) && properties.intAttr?.any (·.value = 0))
      let _ ← MatchProg.root (.arith .addi) #[x, cst.res[0]!] #[returnType]
      return x)
    pure
    (fun x => x)

/-- Rewrite `x * 2` to `x + 3`, creating the constant metadata with a native function. -/
private def nativeApply : Pattern OpCode :=
  Pattern.Builder
    (do
      let returnType ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value returnType
      let cst ← MatchProg.operation (.arith .constant) #[] #[returnType]
        (fun properties => properties.intAttr?.any (·.value = 2))
      let _ ← MatchProg.root (.arith .muli) #[x, cst.res[0]!] #[returnType]
      return (returnType, x, cst.properties))
    (fun (returnType, x, properties) => do
      let (newType, newProperties) ← CreateProg.applyNative (returnType, properties)
        (fun (type, properties) =>
          properties.intAttr?.map fun attr => (type, .int { attr with value := attr.value + 1 }))
      let constant ← CreateProg.operation (.arith .constant) #[] #[newType] (.inr newProperties)
      let add ← CreateProg.operation (.arith .addi) #[x, constant.res[0]!] #[newType]
      return add)
    (fun result => result)

theorem nativeMatch_valid : Pattern.Valid nativeMatch := by
  simp only [nativeMatch]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val _ hinterpCst
  obtain ⟨_, rfl, rfl⟩ := (constant_iff _ _ _).mp hinterpCst
  intro addProp val _ hinterpAddi
  obtain rfl := (addi_iff _ _ _ _ _).mp hinterpAddi
  intro _
  obtain rfl : w = 32 := by grind [IntegerType.signless]
  intro cstPropZero
  grind [add_zero_refines]

/-- A native guard authored after the root can inspect its properties. -/
private def nativeRootGuard (expectNsw : Bool) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let root ← MatchProg.root (.arith .addi) #[x, zero] #[ty]
      MatchProg.matchNative root.properties (fun properties => properties.attr.nsw == expectNsw)
      return x)
    pure
    (fun x => x)

example : (nativeRootGuard false).StructurallyWellFormed := by native_decide

example : (nativeRootGuard false).matcher.ConstrainsRoot := by cbv

/-- Only rewrite an addition whose parent operation has the requested opcode. -/
private def parentOpGuard (parentOpCode : OpCode) : Pattern OpCode :=
  Pattern.Builder
    (do
      let ty ← MatchProg.type (Attr := IntegerType)
      let x ← MatchProg.value ty
      let zero ← matchConstant ty 0
      let root ← MatchProg.root (.arith .addi) #[x, zero] #[ty]
      let () ← MatchProg.inspectOperation (Outputs := Unit) root.op (fun ctx op => do
        let parent ← op.getParentOp! ctx
        guard (parent.getOpType! ctx == parentOpCode))
      return x)
    pure
    (fun x => x)

example (parentOpCode : OpCode) : Pattern.Valid (parentOpGuard parentOpCode) := by
  simp only [parentOpGuard, matchConstant]
  provePuddleValid
  simp only [RuntimeValue.Conforms.integerType,
    forall_exists_index, forall_eq_apply_imp_iff]
  rintro ⟨w⟩ x cstProp val propzero _ hinterpCst
  grind [add_zero_refines, constant_iff, addi_iff]

/- ## Declared-type metadata and verified-operation hypotheses -/

private def typedMatchAssignment (value : RuntimeValue) (operandType resultType : TypeAttr) :
    SemanticAssignment :=
  (SemanticAssignment.empty.bindValue ⟨0⟩ value operandType).bindType ⟨1⟩ resultType

private def typedMatchDecl (opcode : OpCode) : MatchDecl OpCode :=
  .operation opcode #[⟨0⟩] #[⟨1⟩] (fun _ => true) ⟨2⟩ ⟨3⟩ #[⟨4⟩] rfl

private def typedCreateDecl (opcode : OpCode) : CreateDecl OpCode :=
  .operation opcode #[⟨0⟩] #[⟨1⟩] ⟨2⟩ ⟨3⟩ #[⟨4⟩]

/-- The legacy model requires a certificate for the matched operation and attaches its
exact declared result type to the intermediate value. -/
example (opcode : OpCode) (value : RuntimeValue) (operandType resultType : TypeAttr)
    (k : SemanticAssignment → Prop) :
    MatchDecl.Models (typedMatchDecl opcode) (typedMatchAssignment value operandType resultType) k ↔
      ∀ property result,
        IsFromVerifiedOp opcode #[operandType] #[resultType] property →
        InterpretsTo opcode property #[resultType] #[value] #[result] →
        k (((typedMatchAssignment value operandType resultType).bindValue ⟨4⟩ result
          resultType).bindProperty ⟨2⟩ property) := by
  simp [MatchDecl.Models, typedMatchDecl, typedMatchAssignment,
    SemanticAssignment.getValues, SemanticAssignment.getValueTypes, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getValueType, SemanticAssignment.getType,
    SemanticAssignment.bindType, SemanticAssignment.bindValue, SemanticAssignment.bind,
    SemanticAssignment.ForallValues]

/-- A root certificate is required even though CTree root execution is handled separately. -/
example (opcode : OpCode) (value : RuntimeValue) (operandType resultType : TypeAttr)
    (k : SemanticAssignment → Prop) :
    CTree.MatchDecl.Models ⟨3⟩ (typedMatchDecl opcode)
      (typedMatchAssignment value operandType resultType) k ↔
      ∀ property, IsFromVerifiedOp opcode #[operandType] #[resultType] property →
        k ((typedMatchAssignment value operandType resultType).bindProperty ⟨2⟩ property) := by
  simp [CTree.MatchDecl.Models, typedMatchDecl, typedMatchAssignment,
    SemanticAssignment.getValues, SemanticAssignment.getValueTypes, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getValueType, SemanticAssignment.getType,
    SemanticAssignment.bindType, SemanticAssignment.bindValue, SemanticAssignment.bind]

/-- Nested CTree operations also require certificates, and retain declared result types. -/
example (opcode : OpCode) (value : RuntimeValue) (operandType resultType : TypeAttr)
    (k : SemanticAssignment → Prop) :
    CTree.MatchDecl.Models ⟨99⟩ (typedMatchDecl opcode)
      (typedMatchAssignment value operandType resultType) k ↔
      ∀ property, IsFromVerifiedOp opcode #[operandType] #[resultType] property →
        ∀ result, CTree.CanInterpretTo opcode property #[resultType] #[value] (.ok #[result]) →
          k (((typedMatchAssignment value operandType resultType).bindValue ⟨4⟩ result
            resultType).bindProperty ⟨2⟩ property) := by
  simp [CTree.MatchDecl.Models, typedMatchDecl, typedMatchAssignment,
    SemanticAssignment.getValues, SemanticAssignment.getValueTypes, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getValueType, SemanticAssignment.getType,
    SemanticAssignment.bindType, SemanticAssignment.bindValue, SemanticAssignment.bind,
    SemanticAssignment.ForallValues]

private def typedOuterMatchDecl (opcode : OpCode) : MatchDecl OpCode :=
  .operation opcode #[⟨4⟩] #[⟨5⟩] (fun _ => true) ⟨6⟩ ⟨7⟩ #[⟨8⟩] rfl

/-- A nested result's declared type becomes the root's operand type, independently of
which runtime value the nested operation produces. Both operations retain their certificates. -/
example (inner outer : OpCode) (value : RuntimeValue)
    (inputType intermediateType finalType : TypeAttr) (P : Prop) :
    CTree.MatchProg.ModelsDecls ⟨7⟩ [typedMatchDecl inner, typedOuterMatchDecl outer]
      ((typedMatchAssignment value inputType intermediateType).bindType ⟨5⟩ finalType)
      (fun _ => P) ↔
      ∀ innerProperty, IsFromVerifiedOp inner #[inputType] #[intermediateType] innerProperty →
        ∀ intermediate,
          CTree.CanInterpretTo inner innerProperty #[intermediateType] #[value] (.ok #[intermediate]) →
          ∀ outerProperty,
            IsFromVerifiedOp outer #[intermediateType] #[finalType] outerProperty → P := by
  simp [CTree.MatchProg.ModelsDecls, CTree.MatchDecl.Models,
    typedMatchDecl, typedOuterMatchDecl, typedMatchAssignment,
    SemanticAssignment.getValues, SemanticAssignment.getValueTypes, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getValueType, SemanticAssignment.getType,
    SemanticAssignment.bindType, SemanticAssignment.bindValue, SemanticAssignment.bindProperty,
    SemanticAssignment.bind, SemanticAssignment.ForallValues]

/-- Runtime integers carry no signedness; metadata must retain the declared signed type. -/
example :
    (typedMatchAssignment (.int 32 .poison) (TypeAttr.of IntegerType ⟨32, .signed⟩)
      (TypeAttr.of IntegerType ⟨32, .unsigned⟩)).getValueTypes [⟨0⟩] =
      some [TypeAttr.of IntegerType ⟨32, .signed⟩] := rfl

/-- The same runtime pointer can have a declared nonzero address space. -/
example :
    (typedMatchAssignment (.addr .poison) (TypeAttr.of LLVM.PointerType ⟨7⟩)
      (TypeAttr.of LLVM.PointerType ⟨42⟩)).getValueTypes [⟨0⟩] =
      some [TypeAttr.of LLVM.PointerType ⟨7⟩] := rfl

/-- Operation results carry their declared types forward rather than inferring runtime types. -/
example :
    ((SemanticAssignment.bindValues #[.int 32 .poison, .addr .poison] SemanticAssignment.empty
      [⟨0⟩, ⟨1⟩] [TypeAttr.of IntegerType ⟨32, .unsigned⟩,
        TypeAttr.of LLVM.PointerType ⟨42⟩]) >>= fun assignment =>
          assignment.getValueTypes [⟨0⟩, ⟨1⟩]) =
      some [TypeAttr.of IntegerType ⟨32, .unsigned⟩, TypeAttr.of LLVM.PointerType ⟨42⟩] := rfl

/-- An unbound operand rejects the model; every bound value now carries its declared type. -/
example (opcode : OpCode) (resultType : TypeAttr) :
    ¬ CTree.MatchDecl.Models ⟨3⟩ (typedMatchDecl opcode)
      (SemanticAssignment.empty.bindType ⟨1⟩ resultType) (fun _ => True) := by
  simp [CTree.MatchDecl.Models, typedMatchDecl,
    SemanticAssignment.getValues, SemanticAssignment.getValueTypes, SemanticAssignment.getTypes,
    SemanticAssignment.getValue, SemanticAssignment.getValueType, SemanticAssignment.getType,
    SemanticAssignment.bindType, SemanticAssignment.bind, SemanticAssignment.empty]

/-- Creation semantics has no verified-operation assumption: it must establish its own result. -/
example (opcode : OpCode) (value : RuntimeValue) (operandType resultType : TypeAttr)
    (property : propertiesOf opcode) (k : SemanticAssignment → Prop) :
    CreateDecl.semantics (typedCreateDecl opcode)
      ((typedMatchAssignment value operandType resultType).bindProperty ⟨2⟩ property) k ↔
      ∃ result, InterpretsTo opcode property #[resultType] #[value] #[result] ∧
        k (((typedMatchAssignment value operandType resultType).bindProperty ⟨2⟩ property).bindValue
          ⟨4⟩ result resultType) := by
  simp [CreateDecl.semantics, typedCreateDecl, typedMatchAssignment,
    SemanticAssignment.getValues, SemanticAssignment.getTypes, SemanticAssignment.getProperty,
    SemanticAssignment.getValue, SemanticAssignment.getType, SemanticAssignment.bindProperty,
    SemanticAssignment.bindType, SemanticAssignment.bindValue, SemanticAssignment.bind,
    SemanticAssignment.ExistsValues]

/-- CTree creation executes the operation without assuming a verification certificate. -/
example (opcode : OpCode) (value : RuntimeValue) (operandType resultType : TypeAttr)
    (property : propertiesOf opcode) (memory : MemoryState) (α : Type)
    (next : SemanticAssignment → MemoryState → Tree α) :
    CTree.CreateDecl.semantics (typedCreateDecl opcode)
      ((typedMatchAssignment value operandType resultType).bindProperty ⟨2⟩ property) memory next =
      _root_.CTree.bind
        (Veir.CTree.interpretOp' opcode property #[resultType] #[value] #[] memory)
        (fun result => next
          (((typedMatchAssignment value operandType resultType).bindProperty ⟨2⟩ property).bindValue
            ⟨4⟩ result.1[0]! resultType) result.2.1) := by
  simp [CTree.CreateDecl.semantics, typedCreateDecl, typedMatchAssignment,
    SemanticAssignment.getValues, SemanticAssignment.getTypes, SemanticAssignment.getProperty,
    SemanticAssignment.getValue, SemanticAssignment.getType, SemanticAssignment.bindProperty,
    SemanticAssignment.bindType, SemanticAssignment.bindValue, SemanticAssignment.bind]
  rfl

/-- Binding helpers reject missing or surplus types instead of inventing type metadata. -/
example (value : RuntimeValue) (type : TypeAttr) :
    SemanticAssignment.bindValues #[value] SemanticAssignment.empty [⟨0⟩] [] = none ∧
    SemanticAssignment.bindValues #[] SemanticAssignment.empty [] [type] = none := by
  constructor <;> rfl

example (type : TypeAttr) :
    ¬ SemanticAssignment.ForallValues SemanticAssignment.empty [⟨0⟩] [] (fun _ _ => True) ∧
    ¬ SemanticAssignment.ForallValues SemanticAssignment.empty [] [type] (fun _ _ => True) ∧
    ¬ SemanticAssignment.ExistsValues SemanticAssignment.empty [⟨0⟩] [] (fun _ _ => True) ∧
    ¬ SemanticAssignment.ExistsValues SemanticAssignment.empty [] [type] (fun _ _ => True) := by
  simp [SemanticAssignment.ForallValues, SemanticAssignment.ExistsValues]

/-- The verification premise rules out the former i8-to-i64 funnel-shift cases. -/
example (leftProps : propertiesOf (.llvm .intr__fshl : OpCode))
    (rightProps : propertiesOf (.llvm .intr__fshr : OpCode)) :
    ¬ IsFromVerifiedOp (.llvm .intr__fshl)
      #[IntegerType.signless 8, IntegerType.signless 8, IntegerType.signless 8]
      #[IntegerType.signless 64] leftProps ∧
    ¬ IsFromVerifiedOp (.llvm .intr__fshr)
      #[IntegerType.signless 8, IntegerType.signless 8, IntegerType.signless 8]
      #[IntegerType.signless 64] rightProps := by
  constructor
  · intro h
    obtain ⟨ty, operands, results⟩ := h.llvm_fshl_types
    have same : IntegerType.signless 8 = IntegerType.signless 64 :=
      IsTypeAttr.of_injective (by
        simpa using (congrArg (fun types : Array TypeAttr => types[0]!) operands).trans
          (congrArg (fun types : Array TypeAttr => types[0]!) results).symm)
    have width := congrArg IntegerType.bitwidth same
    simp [IntegerType.signless] at width
  · intro h
    obtain ⟨ty, operands, results⟩ := h.llvm_fshr_types
    have same : IntegerType.signless 8 = IntegerType.signless 64 :=
      IsTypeAttr.of_injective (by
        simpa using (congrArg (fun types : Array TypeAttr => types[0]!) operands).trans
          (congrArg (fun types : Array TypeAttr => types[0]!) results).symm)
    have width := congrArg IntegerType.bitwidth same
    simp [IntegerType.signless] at width

/-- A verified word count cannot reinterpret its 64-bit result as i8. -/
example (props : propertiesOf (.gmir_riscv .g_clzw : OpCode)) :
    ¬ IsFromVerifiedOp (.gmir_riscv .g_clzw)
      #[IntegerType.signless 64] #[IntegerType.signless 8] props := by
  intro h
  obtain ⟨sign, _, results⟩ := h.gmir_riscv_clzw_types
  have same : IntegerType.signless 8 = IntegerType.mk 64 sign :=
    IsTypeAttr.of_injective (by
      simpa using congrArg (fun types : Array TypeAttr => types[0]!) results)
  have width := congrArg IntegerType.bitwidth same
  simp [IntegerType.signless] at width

/-- A gMIR constant's attribute and result must have the same integer type. -/
example : ¬ IsFromVerifiedOp (.gmir .g_constant) #[] #[IntegerType.signless 64]
    ⟨⟨0, IntegerType.signless 1⟩⟩ := by
  intro h
  have type := h.gmir_constant_type
  simp [IntegerType.signless] at type

/-- A verified sext-inreg cannot silently change an i128 operand into an i64 result. -/
example (props : propertiesOf (.gmir .g_sext_inreg : OpCode)) :
    ¬ IsFromVerifiedOp (.gmir .g_sext_inreg)
      #[IntegerType.signless 128] #[IntegerType.signless 64] props := by
  intro h
  have same := IsTypeAttr.of_injective h.gmir_sext_inreg_type_eq
  have width := congrArg IntegerType.bitwidth same
  simp [IntegerType.signless] at width

/- ## Test matcher builder validation -/

/-- A matcher that is missing a root declaration. -/
private def missingRootBuilder : MatchProg.Builder Unit := pure ()

#guard_panic in
#eval (MatchProg.build missingRootBuilder).rootHandle.id

/-- A matcher that has a duplicate root declaration. -/
private def duplicateRootBuilder : MatchProg.Builder Unit := do
  let _ ← MatchProg.root (.arith .addi) #[] #[]
  let _ ← MatchProg.root (.arith .addi) #[] #[]
  return ()

#guard_panic in
#eval (MatchProg.build duplicateRootBuilder).rootHandle.id

/- ## Test pattern execution -/

private structure BinaryProgram where
  ctx : WfIRContext OpCode
  moduleOp : OperationPtr

/-- Parse a complete test module. -/
private def parseBinaryProgram (source : String) : Option BinaryProgram := do
  let (ctx, moduleOp, _) ← (parseSourceString source.toUTF8).toOption
  return ⟨ctx, moduleOp⟩

private def addZeroProgram := r#""builtin.module"() ({
  %input = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  %zero = "arith.constant"() <{ value = 0 : i32 }> : () -> i32
  %root = "arith.addi"(%input, %zero) : (i32, i32) -> i32
  "test.test"(%root) : (i32) -> ()
}) : () -> ()"#

private def mulTwoProgram := r#""builtin.module"() ({
  %input = "arith.constant"() <{ value = 42 : i32 }> : () -> i32
  %two = "arith.constant"() <{ value = 2 : i32 }> : () -> i32
  %root = "arith.muli"(%input, %two) : (i32, i32) -> i32
  "test.test"(%root) : (i32) -> ()
}) : () -> ()"#

/-- Parse a program, apply a compiled Puddle pattern, and print the resulting module. -/
private def rewriteAndPrint (source : String) (rule : Pattern OpCode) : IO Unit := do
  let some program := parseBinaryProgram source | IO.println "parse failed"
  let pattern := Pattern.compile rule
  let some ctx := RewritePattern.applyInContext pattern.run program.ctx program.moduleOp | IO.println "rewrite failed"
  Printer.printModule ctx.raw program.moduleOp

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram addZero

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %10 = "arith.addi"(%5, %5) : (i32, i32) -> i32
    "test.test"(%10) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint mulTwoProgram mulTwo

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram nativeMatch

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram (nativeRootGuard false)

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %6 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %7 = "arith.addi"(%5, %6) : (i32, i32) -> i32
    "test.test"(%7) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram (nativeRootGuard true)

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    "test.test"(%5) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram (parentOpGuard (.builtin .module))

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %6 = "arith.constant"() <{"value" = 0 : i32}> : () -> i32
    %7 = "arith.addi"(%5, %6) : (i32, i32) -> i32
    "test.test"(%7) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint addZeroProgram (parentOpGuard (.func .func))

/--
info: "builtin.module"() ({
  ^4():
    %5 = "arith.constant"() <{"value" = 42 : i32}> : () -> i32
    %10 = "arith.constant"() <{"value" = 3 : i32}> : () -> i32
    %11 = "arith.addi"(%5, %10) : (i32, i32) -> i32
    "test.test"(%11) : (i32) -> ()
}) : () -> ()
-/
#guard_msgs in
#eval! rewriteAndPrint mulTwoProgram nativeApply
