module

import all Veir.Passes.InstructionSelection.Proofs.RISCV64.MemoryAddressLemmas
import all Veir.Passes.InstructionSelection.Proofs.RISCV64.Common
import all Veir.Dialects.RISCV.Interpreter
import all Veir.Interpreter.ResultsConformLemmas
import all Veir.Dialects.LLVM.OpInfo
import all Veir.Verifier
import all Veir.GlobalOpInfo
import all Veir.IR.Attribute
import all Veir.Data.RISCV.Reg.Basic
import all Veir.Passes.InstructionSelection.Common
import all Veir.Interfaces.DataLayoutInterfaces
import all Veir.PatternRewriter.Puddle.Builders
import all Veir.Dialects.RISCV.OpInfo
import all Veir.Interpreter.CTreeInterpreter
import all Veir.Dialects.RISCV.Properties
import Init.Data.Nat.Power2.Bitwise
import all Init.Data.Nat.Power2.Basic

/-!
# Validity of RISC-V getelementptr selection

The matcher and creation program allocate handles in loops over the dynamic indices.
We describe their declarations in binding order to check freshness and interpret each loop
by induction. The semantic invariant relates the address register to the LLVM base plus the
scaled indices, modulo the pointer width.
-/

namespace Veir

open Puddle
open Puddle.CTree
attribute [local implicit_reducible] TypeAttr
set_option linter.unusedSimpArgs false

private theorem gep_positions (gep : GetelementptrProperties) (n : Nat) (off : Int)
    (strides : Array Nat) (hd : gepDecomposition? gep n = some (off, strides))
    (hc : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ n) :
    DataLayout.riscv64.gepOffsets gep.elem_type.val
      (GEPIndex.decode gep.rawConstantIndices.values ((Array.range n).map some)) =
      some (off, ((Array.range n).zip strides).map (fun (i, s) => (some i, s))) := by
  rw [decode_map _ _ _ (by simpa using hc), gepOffsets_map]
  unfold gepDecomposition? at hd
  cases he : DataLayout.riscv64.gepOffsets gep.elem_type.val
      (GEPIndex.decode gep.rawConstantIndices.values (Array.range n)) with
  | none => simp [he] at hd
  | some pair =>
    obtain ⟨base, dyn⟩ := pair
    by_cases h : dyn.map Prod.fst = Array.range n
    · simp [he, h, guard, pure] at hd
      obtain ⟨rfl, rfl⟩ := hd
      rw [← h]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
      congr 1
      apply Array.ext <;> simp
    · simp [he, h, guard, failure] at hd

private def signedIndex : Data.LLVM.Int 64 → Option Int
  | .val bits => some bits.toInt
  | .poison => none

/-- Executing the GEP uses the selected strides in operand order, propagating poison. -/
private theorem interpretGEP_decomposed (gep : GetelementptrProperties) (ptr : Data.LLVM.Ptr)
    (idx : Array (Data.LLVM.Int 64)) (res : Array TypeAttr) (memory : MemoryState)
    (off : Int) (strides : Array Nat)
    (hd : gepDecomposition? gep idx.size = some (off, strides))
    (hc : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ idx.size) :
    Llvm.interpretOp' .getelementptr gep res (#[.addr ptr] ++ idx.map (.int 64 ·))
        #[] memory .riscv64 =
      .ok (#[.addr (match ptr, (idx.zip strides).mapM (fun (v, s) =>
          (signedIndex v).map (· * (s : Int))) with
        | .val p, some scaled => .val ⟨UInt64.ofInt (p.address.toNat + off + scaled.foldl (· + ·) 0)⟩
        | _, _ => .poison)], memory, none) := by
  let operands := #[RuntimeValue.addr ptr] ++ idx.map (.int 64 ·)
  have hparts := gep_positions gep idx.size off strides hd hc
  have hindices :
      (((Array.range idx.size).zip strides).map (fun (i, s) => (some i, s))).mapM
        (Llvm.gepIndex operands) =
      some ((idx.zip strides).map (fun (v, s) => (signedIndex v, s))) := by
    apply (Array.mapM_eq_some_iff_of_size_eq (by simp)).mpr
    intro i hi
    simp only [Array.size_map, Array.size_zip, Array.size_range] at hi
    have hi' : i < idx.size := by omega
    simp [operands, Llvm.gepIndex, Llvm.gepOperand, Array.extract_append, getElem!_pos,
      hi, hi']
    cases idx[i] <;> rfl
  dsimp only [operands] at hindices
  cases ptr <;> simp [Llvm.interpretOp', hparts, hindices, Array.mapM_map, Function.comp_def,
    -UInt64.ofInt_add]
  split <;> simp_all

private theorem gep_pointer_types {arg res : TypeAttr} {idx : Array TypeAttr} {gep}
    (h : IsFromVerifiedOp (.llvm .getelementptr) (#[arg] ++ idx) #[res] gep) :
    (∃ p, arg.val = .llvmPointerType p) ∧ (∃ p, res.val = .llvmPointerType p) := by
  rcases h with ⟨ctx, op, hin, hv, hop, hargs, hresults, _⟩
  have ha := congrArg (fun a : Array TypeAttr => a[0]!) hargs
  have hr := congrArg (fun a : Array TypeAttr => a[0]!) hresults
  have na := congrArg Array.size hargs
  have nr := congrArg Array.size hresults
  simp only [OperationPtr.getOperandTypes!.size_eq_getNumOperands!, Array.size_append,
    Array.size_singleton] at na
  simp only [OperationPtr.getResultTypes!.size_eq_getNumResults!, Array.size_singleton] at nr
  rw [OperationPtr.getOperandTypes!.getElem!_eq (by omega : 0 < op.getNumOperands! ctx.raw),
    getElem!_pos _ _ (by simp; omega), Array.getElem_append_left (by simp)] at ha
  change (op.getOperand! ctx.raw 0).getType! ctx.raw = arg at ha
  simp [OperationPtr.getResultTypes!.getElem!_eq (by omega : 0 < op.getNumResults! ctx.raw)] at hr
  simp only [OperationPtr.Verified, OperationPtr.verifyLocalInvariants,
    HasOpInfo.verifyLocalInvariants, ←OperationPtr.getOpType!_eq_getOpType, hop,
    OpCode.verifyLocalInvariants] at hv
  dsimp only [Llvm.verifyLocalInvariants] at hv
  have hv := Except.ok_of_bind_ok hv
  repeat' first | split at hv
                | solve | simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at hv
  exact ⟨ha ▸ verifyLlvmPointerType_ok (Except.ok_left_of_bind_ok hv),
    hr ▸ verifyLlvmPointerType_ok
      (Except.ok_left_of_bind_ok (Except.ok_of_bind_ok (Except.ok_of_bind_ok hv)))⟩

/-- The emitted instructions preserve prior handles and bind the scaled address for the continuation. -/
private theorem addScaled_exec (p i : Handle OpCode .value) (t : Handle OpCode .type)
    (s n : Nat) (a : SemanticAssignment) (mem : MemoryState) (ty : TypeAttr)
    (base index : Data.RISCV.Reg) (hp : a.getValue p = some (.reg base))
    (hi : a.getValue i = some (.reg index)) (ht : a.getType t = some ty)
    (lp : p.id < n) (li : i.id < n) (lt : t.id < n) :
    let built := (addScaled p i t s).run { nextId := n }
    ∃ a', (∀ j < n, a' j = a j) ∧
      a'.getValue built.1 = some (.reg ⟨base.val + index.val * BitVec.ofNat 64 s⟩) ∧
      ∀ {α : Type} (k : SemanticAssignment → MemoryState → Tree α),
        CreateProg.semanticsDecls built.2.decls.reverse a mem k = k a' mem := by
  unfold addScaled
  split <;> (try split)
  all_goals
    simp only [bind, pure, CreateProg.operation, CreateProg.property, Array.size_singleton,
      Array.size_map, Array.size_range, getElem!_pos, Array.getElem_map, Array.getElem_range,
      Nat.zero_lt_one, Nat.add_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.append_nil]
    refine ⟨?_, ?_, ?_, ?_⟩
    rotate_left 3
    intro α k
    simp (disch := omega) [CTree.CreateProg.semanticsDecls, CTree.CreateDecl.semantics, SemanticAssignment.getValues,
      SemanticAssignment.getTypes, SemanticAssignment.bindValues, SemanticAssignment.getProperty,
      SemanticAssignment.bindProperty, SemanticAssignment.bindValue, SemanticAssignment.bind,
      SemanticAssignment.getValue, SemanticAssignment.getType, CTree.interpretOp',
      Riscv.interpretOpCTree, Riscv.interpretOp', ctree_semantics] at *
    simp (disch := omega) [ite_eq_right, hp, hi, ht, List.getElem?_cons_zero, ctree_semantics, SemanticAssignment.bindValues,
      SemanticAssignment.bindValue, SemanticAssignment.bind, SemanticAssignment.getTypes,
      SemanticAssignment.getValues]
    exact rfl
  all_goals first
    | (intro j hj; simp (disch := omega) [SemanticAssignment.bind, ite_eq_right])
    | simp [SemanticAssignment.getValue, SemanticAssignment.bind, Data.RISCV.add, Data.RISCV.sh1add,
        Data.RISCV.sh2add, Data.RISCV.sh3add, Data.RISCV.mul, Data.RISCV.li, Data.RISCV.slli,
        List.getElem?_cons_zero, mkRISCVImm, RISCVImmediateProperties.immField]

  all_goals try solve | rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.add_comm]; rfl
  rename_i h
  rw [Nat.mod_eq_of_lt h.2.2, BitVec.shiftLeft_eq_mul_twoPow]
  obtain ⟨k, eq⟩ := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).mp h.2.1
  rw [eq, Nat.log2_two_pow]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow_eq_ite, show k < 64 by simpa [eq, Nat.log2_two_pow] using h.2.2,
    Nat.mod_eq_of_lt (show 2 ^ k < 2 ^ 64 by apply Nat.pow_lt_pow_right <;> simp_all [Nat.log2_two_pow])]

/-! ## Matcher handles and structural validity -/

private abbrev IndexHandles := Array (Handle OpCode .value)

private def matchIndex (_ : Nat) (ids : IndexHandles) :
    MatchProg.Builder (ForInStep IndexHandles) := do
  let ty ← MatchProg.type (Attr := IntegerType) (·.bitwidth = 64)
  return .yield (ids.push (← MatchProg.value ty))

/-- The matcher allocates a type/value pair for each index, in order. -/
private def indexDecls (n : Nat) : List Nat → List (MatchDecl OpCode)
  | [] => []
  | _ :: xs => .type (fun attr => ((attr.cast? IntegerType).map (fun ty => decide (ty.bitwidth = 64))).getD false) ⟨n⟩ ::
      .value ⟨n⟩ ⟨n + 1⟩ :: indexDecls (n + 2) xs

private def indexIds (n : Nat) : List Nat → List (Handle OpCode .value)
  | [] => []
  | _ :: xs => ⟨n + 1⟩ :: indexIds (n + 2) xs

private theorem matchIndices_run (xs : List Nat) (ids : IndexHandles) (st : MatchProg.BuilderState) :
    (forIn xs ids matchIndex).run st =
      (ids ++ (indexIds st.nextId xs).toArray,
        { st with nextId := st.nextId + 2 * xs.length,
                  decls := (indexDecls st.nextId xs).reverse ++ st.decls }) := by
  induction xs generalizing ids st with
  | nil => simp [List.forIn_nil, pure, indexIds, indexDecls]
  | cons x xs ih =>
    simp only [List.forIn_cons, matchIndex, MatchProg.type, MatchProg.value, bind, pure]
    rw [ih]
    simp [indexDecls, indexIds, Array.push_eq_append, -Array.append_singleton, List.reverse_cons, Nat.mul_add,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc]

private theorem checkIndices (xs : List Nat) (n : Nat) (c : HandleContext)
    (fresh : ∀ j ≥ n, c.lookup j = none) (avail : ∀ j ≥ n, j ∉ c.unavailable) :
    ∃ c', MatchProg.collectDeclBindings (indexDecls n xs) c = some c' ∧
      (∀ j ≥ n + 2 * xs.length, c'.lookup j = none) ∧ c'.unavailable = c.unavailable ∧
      (∀ j < n, c'.lookup j = c.lookup j) ∧
      ∀ h ∈ indexIds n xs, c'.require h = true := by
  induction xs generalizing n c with
  | nil => exact ⟨c, rfl, by simpa using fresh, rfl, by simp, by simp [indexIds]⟩
  | cons x xs ih =>
    let ct : HandleContext := ⟨(n, .type) :: c.bindings, c.unavailable⟩
    let cv : HandleContext := ⟨(n + 1, .value) :: ct.bindings, c.unavailable⟩
    have look (j) : cv.lookup j =
        if n + 1 = j then some .value else if n = j then some .type else c.lookup j := rfl
    have extend : ∀ j ≥ n + 2, cv.lookup j = none := by
      intro j hj
      rw [look]
      simp (disch := omega) [ite_eq_right, fresh]
    obtain ⟨out, hcheck, hfar, hunavail, hlow, hids⟩ :=
      ih (n + 2) cv extend (fun j hj => avail j (by omega))
    refine ⟨out, ?_, by simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfar,
      hunavail, ?_, ?_⟩
    · have hct : ct.lookup (n + 1) = none := by
        change (if n = n + 1 then _ else c.lookup (n + 1)) = none
        simp [fresh]
      have htype : ct.require (⟨n⟩ : Handle OpCode .type) = true := by
        have hlookup : ct.lookup n = some .type := by
          simp [ct, HandleContext.lookup, HandleContext.lookup.lookupBindings]
        simp [HandleContext.require, hlookup, ct, avail]
      simp only [indexDecls, MatchProg.collectDeclBindings, MatchDecl.collectBindings,
        HandleContext.insertFresh, fresh n (by omega)]
      change (do
        let cv' ← (do guard (ct.require (⟨n⟩ : Handle OpCode .type)); ct.insertFresh (⟨n + 1⟩ : Handle OpCode .value))
        MatchProg.collectDeclBindings (indexDecls (n + 2) xs) cv') = some out
      simpa [htype, HandleContext.insertFresh, hct, cv, ct, guard, pure] using hcheck
    · intro j hj
      rw [hlow j (by omega), look]
      simp (disch := omega) [ite_eq_right]
    · intro h hmem
      rcases List.mem_cons.mp hmem with rfl | hmem
      · simp [HandleContext.require, hlow _ (by change n + 1 < n + 2; omega), look,
          hunavail, cv, avail]
      · exact hids h hmem

/-- From the next free identifier onwards, the checker can allocate any handle kind. -/
private def unusedFrom (c : HandleContext) (n : Nat) : Prop :=
  ∀ j ≥ n, c.lookup j = none ∧ j ∉ c.unavailable

/-- Executing a creation step preserves all bindings below its allocation range. -/
private def extendsBelow (c out : HandleContext) (n : Nat) : Prop :=
  out.unavailable = c.unavailable ∧ ∀ j < n, out.lookup j = c.lookup j

private theorem lookup_cons (bs : List (Nat × HandleType OpCode)) (u : List Nat)
    (id : Nat) (kind : HandleType OpCode) (j : Nat) :
    (HandleContext.mk ((id, kind) :: bs) u).lookup j =
      if id = j then some kind else (HandleContext.mk bs u).lookup j := rfl

private theorem addScaled_check (p i : Handle OpCode .value) (t : Handle OpCode .type)
    (s n : Nat) (c : HandleContext) (hf : unusedFrom c n)
    (hp : c.require p) (hi : c.require i) (ht : c.require t)
    (lp : p.id < n) (li : i.id < n) (lt : t.id < n) :
    let built := (addScaled p i t s).run { nextId := n }
    ∃ out, built.2.decls.reverse.foldlM CreateDecl.checkBindings c = some out ∧
      extendsBelow c out n ∧ unusedFrom out built.2.nextId ∧ out.require built.1 ∧
      n ≤ built.2.nextId ∧ built.1.id < built.2.nextId := by
  have fresh (j) (hj : n ≤ j) := (hf j hj).1
  have available (j) (hj : n ≤ j) := (hf j hj).2
  simp only [HandleContext.require, decide_eq_true_eq] at hp hi ht
  unfold addScaled
  split <;> (try split)
  all_goals
    simp only [bind, pure, CreateProg.operation, CreateProg.property, Array.size_singleton,
      Array.size_map, Array.size_range, getElem!_pos, Array.getElem_map, Array.getElem_range,
      Nat.zero_lt_one, Nat.add_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    refine ⟨?_, ?_, ?_, ?_, ?_, by omega, by simp⟩
    rotate_left
    simp (disch := omega) [List.foldlM_cons, CreateDecl.checkBindings, HandleContext.requireMany,
      HandleContext.require, HandleContext.insertManyFresh, HandleContext.insertFresh,
      guard, lookup_cons, ite_eq_right, fresh, available, hp, hi, ht, List.range_succ, pure]
    exact rfl
  all_goals first
    | (refine ⟨rfl, ?_⟩; intro j hj; simp (disch := omega) [lookup_cons, ite_eq_right])
    | (intro j hj; simp (disch := omega) [lookup_cons, ite_eq_right, fresh, available])
    | simp (disch := omega) [HandleContext.require, lookup_cons, available]

private def castReg (v : Handle OpCode .value) (t : Handle OpCode .type) :
    CreateProg.Builder (Handle OpCode .value) := do
  let op ← CreateProg.operation (.builtin .unrealized_conversion_cast) #[v] #[t]
  pure op.res[0]!

private def scaleStep (t : Handle OpCode .type) (pair : Handle OpCode .value × Nat)
    (p : Handle OpCode .value) : CreateProg.Builder (ForInStep (Handle OpCode .value)) := do
  let i ← castReg pair.1 t
  return .yield (← addScaled p i t pair.2)

private theorem addScaled_run_append (p i t s n ds) :
    (addScaled p i t s).run ⟨n, ds⟩ =
      let b := (addScaled p i t s).run ⟨n, []⟩
      (b.1, { b.2 with decls := b.2.decls ++ ds }) := by
  unfold addScaled
  split <;> (try split) <;> rfl

private theorem castReg_check (v t n) (c : HandleContext) (hf : unusedFrom c n)
    (hv : c.require v) (ht : c.require t) (lv : v.id < n) (lt : t.id < n) :
    let b := (castReg v t).run ⟨n, []⟩
    ∃ out, b.2.decls.reverse.foldlM CreateDecl.checkBindings c = some out ∧
      extendsBelow c out n ∧ unusedFrom out (n + 3) ∧ out.require b.1 := by
  have fresh (j) (hj : n ≤ j) := (hf j hj).1
  have av (j) (hj : n ≤ j) := (hf j hj).2
  simp only [HandleContext.require, decide_eq_true_eq] at hv ht
  unfold castReg
  simp only [bind, pure, CreateProg.operation, CreateProg.property, Array.size_singleton,
    Array.size_map, Array.size_range, getElem!_pos, Array.getElem_map, Array.getElem_range,
    Nat.zero_lt_one, Nat.add_zero, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · simp (disch := omega) [CreateDecl.checkBindings, HandleContext.requireMany,
      HandleContext.require, HandleContext.insertManyFresh, HandleContext.insertFresh,
      guard, lookup_cons, ite_eq_right, fresh, av, hv, ht, List.range_succ, pure]
    exact rfl
  · refine ⟨rfl, ?_⟩
    intro j hj
    simp (disch := omega) [lookup_cons, ite_eq_right]
  · intro j hj
    simp (disch := omega) [lookup_cons, ite_eq_right, fresh, av]
  · simp (disch := omega) [HandleContext.require, lookup_cons, av]

private theorem extendsBelow.require {c out : HandleContext} (he : extendsBelow c out n)
    {h : Handle OpCode kind} (hh : c.require h) (hl : h.id < n) : out.require h := by
  simpa only [HandleContext.require, he.1, he.2 _ hl] using hh

private theorem extendsBelow.trans {a b c : HandleContext} (h : extendsBelow a b n)
    (h' : extendsBelow b c m) (hle : n ≤ m) : extendsBelow a c n :=
  ⟨h'.1.trans h.1, fun j hj => (h'.2 j (by omega)).trans (h.2 j hj)⟩

private theorem checkScaleLoop (xs : List (Handle OpCode .value × Nat)) (p t n ds)
    (c : HandleContext) (hf : unusedFrom c n) (hp : c.require p) (ht : c.require t)
    (lp : p.id < n) (lt : t.id < n) (hx : ∀ x ∈ xs, c.require x.1 ∧ x.1.id < n) :
    let b := (forIn xs p (scaleStep t)).run ⟨n, ds⟩
    ∃ new out, b.2.decls = new ++ ds ∧ new.reverse.foldlM CreateDecl.checkBindings c = some out ∧
      extendsBelow c out n ∧ unusedFrom out b.2.nextId ∧ out.require b.1 ∧
      n ≤ b.2.nextId ∧ b.1.id < b.2.nextId := by
  induction xs generalizing p n ds c with
  | nil => exact ⟨[], c, rfl, rfl, ⟨rfl, by simp⟩, hf, hp, Nat.le_refl _, lp⟩
  | cons x xs ih =>
    let cast := (castReg x.1 t).run ⟨n, []⟩
    have hc : (castReg x.1 t).run ⟨n, ds⟩ = (cast.1, ⟨n + 3, cast.2.decls ++ ds⟩) := rfl
    have lc : cast.1.id < n + 3 := by
      simp [cast, castReg, bind, pure, CreateProg.operation, CreateProg.property]
    obtain ⟨cc, hcc, ec, fc, vc⟩ := castReg_check x.1 t n c hf
      (hx x (by simp)).1 ht (hx x (by simp)).2 lt
    let scaled := (addScaled p cast.1 t x.2).run ⟨n + 3, []⟩
    obtain ⟨cs, hcs, es, fs, vs, ns, ls⟩ := addScaled_check p cast.1 t x.2 (n + 3) cc fc
      (ec.require hp lp) vc (ec.require ht lt) (by omega) lc (by omega)
    change n + 3 ≤ scaled.2.nextId at ns
    let ds' := scaled.2.decls ++ (cast.2.decls ++ ds)
    obtain ⟨new, out, eq, chk, et, ft, vt, nt, last⟩ := ih scaled.1 scaled.2.nextId ds' cs fs vs
      (es.require (ec.require ht lt) (by omega)) ls (by omega) (by
        intro y hy
        have ⟨req, low⟩ := hx y (by simp [hy])
        exact ⟨es.require (ec.require req low) (by omega), by omega⟩)
    simp only [List.forIn_cons, scaleStep, bind, pure, hc]
    simp only [addScaled_run_append p cast.1 t x.2 (n + 3) (cast.2.decls ++ ds)]
    refine ⟨new ++ scaled.2.decls ++ cast.2.decls, out, ?_, ?_, ?_, ft, vt, Nat.le_trans (by omega) nt, last⟩
    · simpa [ds', List.append_assoc] using eq
    · change cast.2.decls.reverse.foldlM CreateDecl.checkBindings c = some cc at hcc
      change scaled.2.decls.reverse.foldlM CreateDecl.checkBindings cc = some cs at hcs
      simp only [List.reverse_append, List.foldlM_append, hcc, Option.bind_eq_bind, Option.bind_some, hcs, chk]
    · exact (ec.trans es (by omega)).trans et (by omega)

private theorem matchIndices_builder (xs : List Nat) (ids : IndexHandles) :
    forIn xs ids matchIndex = ⟨fun st =>
      (ids ++ (indexIds st.nextId xs).toArray,
        { st with nextId := st.nextId + 2 * xs.length,
                  decls := (indexDecls st.nextId xs).reverse ++ st.decls })⟩ := by
  exact congrArg MatchProg.Builder.mk (funext (matchIndices_run xs ids))

/-- Handles 0 and 1 bind the base type and value. Each dynamic index binds two more handles. -/
private abbrev endIndices (ss : Array Nat) := 2 + 2 * ss.toList.length

private theorem indexIds_lt (n : Nat) (xs : List Nat) :
    ∀ h ∈ indexIds n xs, h.id < n + 2 * xs.length := by
  induction xs generalizing n with
  | nil => simp [indexIds]
  | cons x xs ih =>
    intro h hm
    rcases List.mem_cons.mp hm with rfl | hm
    · simp; omega
    · have := ih (n + 2) h hm
      simp; omega

private theorem collect_append (xs ys : List (MatchDecl OpCode)) (c : HandleContext) :
    MatchProg.collectDeclBindings (xs ++ ys) c =
      (MatchProg.collectDeclBindings xs c).bind (MatchProg.collectDeclBindings ys) := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp [MatchProg.collectDeclBindings, ih, Option.bind_assoc]

private theorem bindingDecls_indices (n : Nat) (xs : List Nat) :
    (indexDecls n xs).all (fun d => match d with
      | .type .. | .value .. => true | _ => false) := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih => simpa [indexDecls] using ih (n + 2)

private def anyType (t : TypeAttr) := ((t.cast? TypeAttr).map (fun _ => true)).getD false

private def gepRootDecl (ss : Array Nat) : MatchDecl OpCode :=
  let n := endIndices ss
  .operation (.llvm .getelementptr) (#[⟨1⟩] ++ (indexIds 2 ss.toList).toArray) #[⟨n⟩]
    (fun _ => true) ⟨n + 3⟩ ⟨n + 1⟩ #[⟨n + 2⟩] (by simp)

private def gepGuard (ss : Array Nat) (kind : GEPOffset) : MatchDecl OpCode :=
  .applyNative (⟨endIndices ss + 3⟩ : Handle OpCode (.prop (.llvm .getelementptr))) fun prop =>
    match gepDecomposition? prop ss.size with
    | some (off, strides) => decide (strides = ss ∧ gepOffsetKind off = kind)
    | none => false

private theorem gep_matcher_shape (ss : Array Nat) (kind : GEPOffset) :
    let m := (getelementptr_pattern ss kind).matcher
    m.rootHandle = ⟨endIndices ss + 1⟩ ∧
      m.decls = gepRootDecl ss :: .type anyType ⟨endIndices ss⟩ ::
        ((indexDecls 2 ss.toList).reverse ++ [.value ⟨0⟩ ⟨1⟩, .type anyType ⟨0⟩, gepGuard ss kind]) := by
  have h := matchIndices_builder ss.toList #[]
  unfold matchIndex at h
  generalize he : getelementptr_pattern ss kind = pat
  unfold getelementptr_pattern at he
  simp only [← Array.forIn_toList, h] at he
  subst pat
  simp only [Pattern.Builder, MatchProg.build, MatchProg.root, MatchProg.value, MatchProg.type,
    MatchProg.matchNative, bind, pure, gepRootDecl, gepGuard, endIndices, anyType, List.append_assoc,
    Nat.reduceAdd, Array.empty_append, Array.size_singleton, List.cons_append, List.nil_append,
    List.reverse_singleton, List.reverse_nil, List.reverse_cons, List.append_nil]
  have hr (f : Nat → Handle OpCode .value) : (Array.range 1).map f = #[f 0] := by
    apply Array.ext <;> simp
  simp [hr]
  refine ⟨rfl, ?_⟩
  funext prop
  cases he : gepDecomposition? prop ss.size <;> simp [he]

private theorem getelementptr_constrainsRoot (ss : Array Nat) (kind : GEPOffset) :
    (getelementptr_pattern ss kind).matcher.ConstrainsRoot := by
  simp only [MatchProg.ConstrainsRoot, (gep_matcher_shape ss kind).1,
    (gep_matcher_shape ss kind).2, gepRootDecl]

private theorem gep_bindingDecls (ss : Array Nat) (kind : GEPOffset) :
    (getelementptr_pattern ss kind).matcher.bindingDecls =
      .type anyType ⟨0⟩ :: .value ⟨0⟩ ⟨1⟩ :: (indexDecls 2 ss.toList ++
        [.type anyType ⟨endIndices ss⟩, gepRootDecl ss, gepGuard ss kind]) := by
  rw [MatchProg.bindingDecls, (gep_matcher_shape ss kind).2]
  let ds := indexDecls 2 ss.toList
  have select (f : MatchDecl OpCode → Bool) (b : Bool)
      (h₁ : ∀ m t, f (.type m t) = b) (h₂ : ∀ t v, f (.value t v) = b) :
      ds.filter f = if b then ds else [] := by
    have hf (d) (hd : d ∈ ds) : f d = b := by
      have h := List.all_eq_true.mp (bindingDecls_indices 2 ss.toList) d hd
      cases d <;> simp_all
    cases b
    · exact List.filter_eq_nil_iff.mpr (fun d hd => by simp [hf d hd])
    · exact List.filter_eq_self.mpr hf
  simp only [List.partition_eq_filter_filter, List.filter_cons, List.filter_append, List.filter_reverse,
    Function.comp_apply, gepRootDecl, gepGuard, Bool.not_true, Bool.not_false, Bool.false_eq_true,
    ↓reduceIte, List.filter_nil, List.reverse_cons, List.reverse_append, List.reverse_nil,
    List.nil_append, List.cons_append, List.append_assoc, List.append_nil]
  rw [select _ true (by intros; rfl) (by intros; rfl), select _ false (by intros; rfl) (by intros; rfl)]
  simp [ds]

private theorem gep_matcher_checks (strides : Array Nat) (offset : GEPOffset) :
    let n := endIndices strides
    ∃ c, (getelementptr_pattern strides offset).matcher.collectBindings = some c ∧
      unusedFrom c (n + 4) ∧ c.require (⟨1⟩ : Handle OpCode .value) ∧
      c.require (⟨n⟩ : Handle OpCode .type) ∧
      c.require (⟨n + 3⟩ : Handle OpCode (.prop (.llvm .getelementptr))) ∧
      ∀ h ∈ indexIds 2 strides.toList, c.require h := by
  dsimp only
  simp only [MatchProg.collectBindings, MatchProg.rootResults?, (gep_matcher_shape strides offset).1,
    (gep_matcher_shape strides offset).2, gep_bindingDecls, gepRootDecl, ↓reduceIte,
    bind, pure, Option.bind_some, gepGuard]
  let xs := strides.toList
  let n := endIndices strides
  let c₀ : HandleContext := ⟨[(1, .value), (0, .type)], []⟩
  obtain ⟨ci, hci, hf, hu, hl, hh⟩ := checkIndices xs 2 c₀ (by
    intro j hj
    simp (disch := omega) [c₀, HandleContext.lookup, HandleContext.lookup.lookupBindings, ite_eq_right])
    (by simp [c₀])
  change ∀ j ≥ n, ci.lookup j = none at hf
  have hp : ci.lookup 1 = some .value := hl 1 (by decide)
  have first (m : TypeMatcher) (rest : List (MatchDecl OpCode)) :
      MatchProg.collectDeclBindings (.type m ⟨0⟩ :: .value ⟨0⟩ ⟨1⟩ :: rest) .empty =
        MatchProg.collectDeclBindings rest c₀ := rfl
  simp only [first, collect_append]
  change MatchProg.collectDeclBindings (indexDecls 2 strides.toList) c₀ = some ci at hci
  rw [hci]
  change ∀ j ≥ endIndices strides, ci.lookup j = none at hf
  have hn : 2 ≤ endIndices strides := by unfold endIndices; omega
  rcases ci with ⟨bs, us⟩
  change us = [] at hu
  subst us
  let ci : HandleContext := ⟨bs, []⟩
  have small (h) (hm : h ∈ indexIds 2 strides.toList) : h.id < endIndices strides :=
    indexIds_lt 2 strides.toList h hm
  have known (h) (hm : h ∈ indexIds 2 strides.toList) := (hh h hm)
  simp only [HandleContext.require, decide_eq_true_eq] at known
  have hrequire : ∀ h ∈ indexIds 2 strides.toList,
      (if endIndices strides = h.id then some HandleType.type else ci.lookup h.id) = some .value := by
    intro h hm
    rw [ite_eq_right (Nat.ne_of_gt (small h hm))]
    exact (known h hm).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  rotate_left
  · simp (disch := omega) [MatchProg.collectDeclBindings, MatchDecl.collectBindings,
      HandleContext.requireMany, HandleContext.require, HandleContext.insertFresh,
      HandleContext.insertManyFresh, lookup_cons, hf, hp, guard, hrequire, List.range_succ,
      MetadataTuple.Shape.requireBindings, IsMetadataTuple.shape_property, HandleContext.forbidMany,
      HandleContext.forbid, pure, ite_eq_right]
    rw [ite_eq_left hrequire]
    simp [lookup_cons, Option.bind_some]
    exact rfl
  all_goals try (intro j hj)
  all_goals try have low := small j hj
  all_goals simp (disch := omega) [HandleContext.require, lookup_cons, ite_eq_right, List.mem_cons]
  all_goals try have hit := (known j hj).1
  all_goals simp only [HandleContext.lookup] at *
  all_goals solve | (constructor <;> first | assumption | apply hf <;> omega | omega) | omega

private def finishGEP (offset : GEPOffset) (count : Nat)
    (gep : Handle OpCode (.prop (.llvm .getelementptr))) (reg res : Handle OpCode .type)
    (addr : Handle OpCode .value) : CreateProg.Builder CreatedOpHandle := do
  let addr ← match offset with
    | .zero => pure addr
    | .imm => do
      let imm ← gepOffsetImm .addi rfl count gep
      let op ← CreateProg.operation (.riscv .addi) #[addr] #[reg] imm
      pure op.res[0]!
    | .wide => do
      let imm ← gepOffsetImm .li rfl count gep
      let li ← CreateProg.operation (.riscv .li) #[] #[reg] imm
      let add ← CreateProg.operation (.riscv .add) #[addr, li.res[0]!] #[reg]
      pure add.res[0]!
  CreateProg.operation (.builtin .unrealized_conversion_cast) #[addr] #[res]

private def prefixGEP (n : Nat) : CreateProg.BuilderState :=
  let (t, st) := (CreateProg.type (RegisterType.mk none)).run ⟨n + 4, []⟩
  ((castReg ⟨1⟩ t).run st).2

/-- After the index handles, the matcher allocates the result type, root, root result, and
properties. Creation then allocates the register type and the three handles of the base cast. -/
private def builtGEP (ss : Array Nat) (offset : GEPOffset) :=
  let n := endIndices ss
  let xs := ((indexIds 2 ss.toList).toArray.zip ss).toList
  let loop := (forIn xs ⟨n + 7⟩ (scaleStep ⟨n + 4⟩)).run (prefixGEP n)
  (finishGEP offset ss.size ⟨n + 3⟩ ⟨n + 4⟩ ⟨n⟩ loop.1).run loop.2

private theorem gep_creation (ss : Array Nat) (offset : GEPOffset) :
    (getelementptr_pattern ss offset).creation.decls = (builtGEP ss offset).2.decls.reverse ∧
    (getelementptr_pattern ss offset).replacement.values = (builtGEP ss offset).1.res := by
  have h := matchIndices_builder ss.toList #[]
  unfold matchIndex at h
  generalize he : getelementptr_pattern ss offset = pat
  unfold getelementptr_pattern at he
  simp only [← Array.forIn_toList, h] at he
  subst pat
  cases offset <;>
    simp +unfoldPartialApp only [Pattern.Builder, MatchProg.build, CreateProg.build, bind, pure, MatchProg.type,
      MatchProg.root, MatchProg.value, MatchProg.matchNative, Array.empty_append, Array.size_singleton,
      Nat.reduceAdd, builtGEP, prefixGEP, castReg, CreateProg.type, CreateProg.operation,
      CreateProg.property, Array.size_map, Array.size_range, getElem!_pos, Nat.zero_lt_one,
      Array.getElem_map, Array.getElem_range, Nat.add_zero, finishGEP, scaleStep, endIndices]
  all_goals constructor <;> trivial

private theorem finishGEP_check (offset count gep reg res addr n ds)
    (c₀ c : HandleContext) (hds : ds.reverse.foldlM CreateDecl.checkBindings c₀ = some c)
    (hf : unusedFrom c n) (hg : c.require gep) (hr : c.require reg)
    (hs : c.require res) (ha : c.require addr)
    (lr : reg.id < n) (ls : res.id < n) (la : addr.id < n) :
    let b := (finishGEP offset count gep reg res addr).run ⟨n, ds⟩
    ∃ out, b.2.decls.reverse.foldlM CreateDecl.checkBindings c₀ = some out ∧
      out.requireMany b.1.res.toList := by
  have fresh (j) (hj : n ≤ j) := (hf j hj).1
  have av (j) (hj : n ≤ j) := (hf j hj).2
  simp only [HandleContext.require, decide_eq_true_eq] at hg hr hs ha
  cases offset <;>
    simp only [finishGEP, gepOffsetImm, bind, pure, CreateProg.applyNative, MetadataTuple.fresh,
      IsMetadataTuple.shape_property, MetadataTuple.Shape.fresh, MetadataTuple.Atom.fresh,
      CreateProg.operation, CreateProg.property, Array.size_singleton, Array.size_map,
      Array.size_range, getElem!_pos, Array.getElem_map, Array.getElem_range,
      Nat.zero_lt_one, Nat.add_zero, List.reverse_cons, List.foldlM_append, hds,
      Option.bind_eq_bind, Option.bind_some, Array.toList_map, Array.toList_range,
      List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    simp (disch := omega) [CreateDecl.checkBindings, HandleContext.requireMany, guard, pure,
      HandleContext.require, HandleContext.insertFresh, HandleContext.insertManyFresh,
      MetadataTuple.Shape.requireBindings, MetadataTuple.Shape.insertFreshBindings,
      IsMetadataTuple.shape_property, lookup_cons, ite_eq_right, fresh, av, hg, hr, hs, ha,
      List.range_succ]
    exact rfl
  all_goals simp (disch := omega) [HandleContext.requireMany, HandleContext.require, lookup_cons, av]

private theorem getelementptr_structurallyWellFormed (ss : Array Nat) (offset : GEPOffset) :
    (getelementptr_pattern ss offset).StructurallyWellFormed := by
  let n := endIndices ss
  obtain ⟨c, hm, hf, hp, hr, hg, hi⟩ := gep_matcher_checks ss offset
  have fresh (j) (hj : n + 4 ≤ j) := (hf j hj).1
  have av (j) (hj : n + 4 ≤ j) := (hf j hj).2
  have hn : 2 ≤ n := by dsimp [n, endIndices]; omega
  let reg : Handle OpCode .type := ⟨n + 4⟩
  let ct : HandleContext := ⟨(n + 4, .type) :: c.bindings, c.unavailable⟩
  have hct : unusedFrom ct (n + 5) := by
    intro j hj
    simp (disch := omega) [ct, lookup_cons, ite_eq_right, fresh, av]
  have er : extendsBelow c ct (n + 4) := ⟨rfl, by
    intro j hj; simp (disch := omega) [ct, lookup_cons, ite_eq_right]⟩
  have hreg : ct.require reg := by simp [reg, ct, HandleContext.require, lookup_cons, av]
  obtain ⟨cc, hc, ec, fc, vc⟩ := castReg_check ⟨1⟩ reg (n + 5) ct hct
    (er.require hp (by change 1 < n + 4; omega)) hreg (by change 1 < n + 5; omega) (by simp [reg])
  have castId : ((castReg ⟨1⟩ reg).run ⟨n + 5, []⟩).1 = ⟨n + 7⟩ := by
    simp [castReg, bind, pure, CreateProg.operation, CreateProg.property]
  rw [castId] at vc
  have pre : (prefixGEP n).decls.reverse.foldlM CreateDecl.checkBindings c = some cc := by
    have he : (prefixGEP n).decls.reverse =
        [.type (TypeAttr.of RegisterType {}) reg] ++ ((castReg ⟨1⟩ reg).run ⟨n + 5, []⟩).2.decls.reverse := by
      simp [prefixGEP, castReg, reg, CreateProg.type, CreateProg.operation, CreateProg.property,
        pure, bind]
    rw [he, List.foldlM_append]
    simpa [CreateDecl.checkBindings, HandleContext.insertFresh, reg, fresh, ct] using hc
  let xs := ((indexIds 2 ss.toList).toArray.zip ss).toList
  obtain ⟨new, out, eq, chk, et, ft, vt, nt, last⟩ := checkScaleLoop xs ⟨n + 7⟩ reg (n + 8)
    (prefixGEP n).decls cc fc vc (ec.require hreg (by simp [reg]))
    (by simp) (by simp [reg]) (by
      intro x hx
      have hx' : x.1 ∈ indexIds 2 ss.toList := by
        have := List.of_mem_zip (by simpa [xs] using hx : x ∈ (indexIds 2 ss.toList).zip ss.toList)
        exact this.1
      have hl : x.1.id < n := indexIds_lt 2 ss.toList _ hx'
      exact ⟨ec.require (er.require (hi _ hx') (by omega)) (by omega), by omega⟩)
  let loop := (forIn xs ⟨n + 7⟩ (scaleStep reg)).run (prefixGEP n)
  change loop.2.decls = new ++ (prefixGEP n).decls at eq
  change n + 8 ≤ loop.2.nextId at nt
  have preloop : loop.2.decls.reverse.foldlM CreateDecl.checkBindings c = some out := by
    rw [eq, List.reverse_append, List.foldlM_append, pre]
    exact chk
  have allOld := (er.trans ec (by omega)).trans et (by omega)
  obtain ⟨doneC, hd, hv⟩ := finishGEP_check offset ss.size ⟨n + 3⟩ reg ⟨n⟩ loop.1 loop.2.nextId
    loop.2.decls c out preloop ft (allOld.require hg (by simp))
    (et.require (ec.require hreg (by simp [reg])) (by simp [reg]))
    (allOld.require hr (by simp)) vt
    (by dsimp [reg]; omega) (by change n < loop.2.nextId; omega) last
  obtain ⟨cd, cr⟩ := gep_creation ss offset
  unfold Pattern.StructurallyWellFormed Pattern.checkStructure
  simp only [hm, Option.bind_some, CreateProg.checkBindings, cd, Replacement.checkBindings, cr]
  change (builtGEP ss offset).2.decls.reverse.foldlM CreateDecl.checkBindings c = some doneC at hd
  change doneC.requireMany (builtGEP ss offset).1.res.toList = true at hv
  simp only [bind, Option.bind_some, hm, hd, hv, guard, ↓reduceIte, pure, Option.isSome_some]

private def supportedCreate : CreateDecl OpCode → Prop
  | .operation op .. => HasOpInfo.isTerminator op = false
  | _ => True

private theorem supportedLoop (xs : List (Handle OpCode .value × Nat)) (p t n ds)
    (ok : ∀ d ∈ ds, supportedCreate d) :
    ∀ d ∈ ((forIn xs p (scaleStep t)).run ⟨n, ds⟩).2.decls, supportedCreate d := by
  induction xs generalizing p n ds with
  | nil => exact ok
  | cons x xs ih =>
    simp only [List.forIn_cons, scaleStep, castReg, bind, pure, CreateProg.operation, CreateProg.property]
    apply ih
    unfold addScaled
    split <;> (try split) <;> simp [bind, pure, CreateProg.operation, CreateProg.property,
      List.forall_mem_cons, supportedCreate, is_terminator]
    all_goals exact ok

private theorem getelementptr_supported (ss : Array Nat) (offset : GEPOffset) :
    CTree.Pattern.Supported (getelementptr_pattern ss offset) := by
  constructor
  · rw [(gep_matcher_shape ss offset).2]
    simp [gepRootDecl, gepGuard, List.forall_mem_cons, is_terminator]
    intro d hd
    rcases hd with hd | rfl | rfl | rfl <;> try trivial
    have h := List.all_eq_true.mp (bindingDecls_indices 2 ss.toList) d hd
    cases d <;> trivial
  · rw [(gep_creation ss offset).1]
    simp only [List.mem_reverse]
    let n := endIndices ss
    have ok : ∀ d ∈ (prefixGEP n).decls, supportedCreate d := by
      simp [prefixGEP, castReg, CreateProg.type, CreateProg.operation, CreateProg.property, bind, pure,
        List.forall_mem_cons, supportedCreate, is_terminator]
    have hl := supportedLoop ((indexIds 2 ss.toList).toArray.zip ss).toList ⟨n + 7⟩ ⟨n + 4⟩
      (n + 8) (prefixGEP n).decls ok
    change ∀ d ∈ ((forIn _ _ (scaleStep ⟨n + 4⟩)).run (prefixGEP n)).2.decls, supportedCreate d at hl
    dsimp only [n] at hl
    change ∀ d ∈ (builtGEP ss offset).2.decls, supportedCreate d
    unfold builtGEP
    cases offset <;> simp [finishGEP, gepOffsetImm, CreateProg.applyNative, CreateProg.operation,
      CreateProg.property, bind, pure, List.forall_mem_cons, supportedCreate, is_terminator]
    all_goals simpa only [Array.toList_zip, List.toList_toArray, supportedCreate, is_terminator] using hl

/-! ## Simulation of the generated instructions -/

private abbrev Word := BitVec 64
private abbrev Index := Data.LLVM.Int 64

private def indexWord : Index → Option Word
  | .poison => none
  | .val w => some w

private def ptrWord : Data.LLVM.Ptr → Option Word
  | .poison => none
  | .val p => some p.address.toBitVec

/-- A defined source fixes the register bits. Poison permits every register value. -/
private def realizes (source : Option Word) (w : Word) : Prop :=
  ∀ b, source = some b → w = b

private theorem castReg_sim (v : Handle OpCode .value) (t : Handle OpCode .type) (n : Nat)
    (a : SemanticAssignment) (mem : MemoryState) (val : Data.LLVM.Ptr ⊕ Index)
    (hv : a.getValue v = some (val.elim RuntimeValue.addr (.int 64 ·)))
    (ht : a.getType t = some (TypeAttr.of RegisterType {}))
    (lv : v.id < n) (lt : t.id < n) {R : α → β → Prop} (source : Tree β)
    (k : SemanticAssignment → MemoryState → Tree α)
    (hk : ∀ a' bits, (∀ j < n, a' j = a j) →
      a'.getValue ((castReg v t).run ⟨n, []⟩).1 = some (.reg ⟨bits⟩) →
      realizes (val.elim ptrWord indexWord) bits → _root_.CTree.Sim R (k a' mem) source) :
    _root_.CTree.Sim R
      (CTree.CreateProg.semanticsDecls ((castReg v t).run ⟨n, []⟩).2.decls.reverse a mem k) source := by
  simp only [SemanticAssignment.getValue, SemanticAssignment.getType] at hv ht
  simp only [castReg, bind, pure, CreateProg.operation, CreateProg.property, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append]
  simp (disch := omega) [CTree.CreateProg.semanticsDecls, CTree.CreateDecl.semantics, SemanticAssignment.getTypes,
    SemanticAssignment.getValues, SemanticAssignment.getProperty, SemanticAssignment.bindProperty,
    SemanticAssignment.bindValues, SemanticAssignment.bindValue, SemanticAssignment.bind,
    SemanticAssignment.getValue, SemanticAssignment.getType, ite_eq_right, hv, ht, List.range_succ,
    CTree.interpretOp', Builtin.interpretOpCTree, Builtin.interpretUnrealizedConversionCastCTree,
    Attribute.of_def, -Attribute.registerType_eq_of]
  cases val <;> rename_i value <;> cases value
  all_goals
    simp [Sum.elim, List.getElem?_cons_zero, Attribute.of_def, -Attribute.registerType_eq_of,
      Builtin.intToRegCTree, Functor.map, CTree.CTree.choose_def, CTree.CTree.tau_def,
      _root_.CTree.Sim.tau_l, _root_.CTree.CTree.bind_tau, ctree_semantics,
      SemanticAssignment.bindValues, SemanticAssignment.bindValue]
    try intro bits
    apply hk
    · intro j hj
      simp (disch := omega) [SemanticAssignment.bind, ite_eq_right]
    · simp [castReg, bind, pure, CreateProg.operation, CreateProg.property,
        SemanticAssignment.getValue, SemanticAssignment.bind, getElem!_pos]
      rfl
    · simp [realizes, ptrWord, indexWord]

private theorem semanticsDecls_append (xs ys : List (CreateDecl OpCode)) (a : SemanticAssignment)
    (mem : MemoryState) (k : SemanticAssignment → MemoryState → Tree α) :
    CTree.CreateProg.semanticsDecls (xs ++ ys) a mem k =
      CTree.CreateProg.semanticsDecls xs a mem (fun a' m => CTree.CreateProg.semanticsDecls ys a' m k) := by
  induction xs generalizing a mem with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, CTree.CreateProg.semanticsDecls, ih]

private abbrev ScaleInputs := List (Handle OpCode .value × Nat)
private def scaledLoop (xs : ScaleInputs) (p t n) := (forIn xs p (scaleStep t)).run ⟨n, []⟩

private theorem scaleLoop_run_append (xs : ScaleInputs) (p t n ds) :
    (forIn xs p (scaleStep t)).run ⟨n, ds⟩ =
      let b := scaledLoop xs p t n
      (b.1, ⟨b.2.nextId, b.2.decls ++ ds⟩) := by
  induction xs generalizing p n ds with
  | nil => rfl
  | cons x xs ih =>
    let cast := (castReg x.1 t).run ⟨n, []⟩
    have hc (ds) : (castReg x.1 t).run ⟨n, ds⟩ = (cast.1, ⟨n + 3, cast.2.decls ++ ds⟩) := rfl
    unfold scaledLoop
    simp only [List.forIn_cons, scaleStep, bind, pure, hc, List.append_nil]
    simp only [addScaled_run_append p cast.1 t x.2 (n + 3) (cast.2.decls ++ ds),
      addScaled_run_append p cast.1 t x.2 (n + 3) cast.2.decls]
    simp only [ih, List.append_assoc]

private def addWord (b : Option Word) (v : Index) (s : Nat) : Option Word := do
  return (← b) + (← indexWord v) * BitVec.ofNat 64 s

private def applyStrides (b : Option Word) (xs : List (Index × Nat)) : Option Word :=
  xs.foldl (fun acc (v,s) => addWord acc v s) b

private theorem realizes_add {b : Option Word} {v : Index} {base bits : Word}
    (hb : realizes b base) (hi : realizes (indexWord v) bits) (s : Nat) :
    realizes (addWord b v s) (base + bits * BitVec.ofNat 64 s) := by
  cases b <;> cases v <;> simp_all [realizes, addWord, indexWord]

private theorem addScaled_ids (p i t s n) :
    let b := (addScaled p i t s).run ⟨n, []⟩
    n ≤ b.2.nextId ∧ b.1.id < b.2.nextId := by
  unfold addScaled
  split <;> (try split) <;> simp [bind, pure, CreateProg.operation, CreateProg.property] <;> omega

private theorem getValues_agree {a a' : SemanticAssignment} {n : Nat} {ids : List (Handle OpCode .value)}
    (he : ∀ j < n, a' j = a j) (hl : ∀ h ∈ ids, h.id < n) :
    a'.getValues ids = a.getValues ids := by
  induction ids with
  | nil => rfl
  | cons h ids ih =>
    simp only [SemanticAssignment.getValues, List.mapM_cons, SemanticAssignment.getValue,
      he h.id (hl h (by simp))]
    rw [show ids.mapM a'.getValue = ids.mapM a.getValue from ih (by grind)]

/-- The address register realizes the sum of the processed indices. All older handles retain
their bindings, so the continuation can still read the GEP properties and result type. -/
private theorem scaleLoop_sim (xs : ScaleInputs) (p t n) (a : SemanticAssignment) (mem : MemoryState)
    (values : List Index) (base : Word) (src : Option Word) (hb : realizes src base)
    (hp : a.getValue p = some (.reg ⟨base⟩)) (ht : a.getType t = some (TypeAttr.of RegisterType {}))
    (hx : a.getValues (xs.map Prod.fst) = some (values.map (.int 64 ·)))
    (lp : p.id < n) (lt : t.id < n) (lx : ∀ x ∈ xs, x.1.id < n)
    {R : α → β → Prop} (source : Tree β) (k : SemanticAssignment → MemoryState → Tree α)
    (hk : ∀ a' bits, (∀ j < n, a' j = a j) →
      a'.getValue (scaledLoop xs p t n).1 = some (.reg ⟨bits⟩) →
      realizes (applyStrides src (values.zip (xs.map Prod.snd))) bits → _root_.CTree.Sim R (k a' mem) source) :
    _root_.CTree.Sim R (CTree.CreateProg.semanticsDecls
      (scaledLoop xs p t n).2.decls.reverse a mem k) source := by
  induction xs generalizing values src base p n a with
  | nil => exact hk a base (by simp) hp (by simpa [applyStrides] using hb)
  | cons x xs ih =>
    change ((x.1 :: xs.map Prod.fst).mapM a.getValue) = _ at hx
    cases hv : a.getValue x.1 <;> simp only [List.mapM_cons, hv, Option.bind_eq_bind,
      Option.bind_none, Option.bind_some, reduceCtorEq] at hx
    cases hvs : a.getValues (xs.map Prod.fst) <;>
      simp only [SemanticAssignment.getValues] at hvs <;>
      simp only [hvs, Option.pure_def, Option.bind_none, Option.bind_some, reduceCtorEq, Option.some.injEq] at hx
    cases values <;> simp only [List.map_nil, List.map_cons, List.cons.injEq, reduceCtorEq] at hx
    rename_i v vs
    obtain ⟨rfl, rfl⟩ := hx
    let cast := (castReg x.1 t).run ⟨n, []⟩
    let scaled := (addScaled p cast.1 t x.2).run ⟨n + 3, []⟩
    let tail := scaledLoop xs scaled.1 t scaled.2.nextId
    have headRun : scaledLoop (x :: xs) p t n =
        (tail.1, ⟨tail.2.nextId, tail.2.decls ++ (scaled.2.decls ++ cast.2.decls)⟩) := by
      unfold scaledLoop
      simp only [List.forIn_cons, scaleStep, bind, pure]
      let b := (addScaled p cast.1 t x.2).run ⟨n + 3, cast.2.decls⟩
      change (forIn xs b.1 (scaleStep t)).run b.2 = _
      dsimp only [b]
      rw [addScaled_run_append]
      exact scaleLoop_run_append xs _ _ _ _
    rw [headRun] at hk ⊢
    simp only [List.reverse_append, semanticsDecls_append]
    apply castReg_sim x.1 t n a mem (.inr v) hv ht (lx _ (by simp)) lt source
    intro ac bits ec hv' hi
    have hbase : ac.getValue p = some (.reg ⟨base⟩) := by
      simpa only [SemanticAssignment.getValue, ec _ lp] using hp
    have htype : ac.getType t = some (TypeAttr.of RegisterType {}) := by
      simpa only [SemanticAssignment.getType, ec _ lt] using ht
    have lc : cast.1.id < n + 3 := by simp [cast, castReg, bind, pure, CreateProg.operation, CreateProg.property]
    obtain ⟨as', es, hs, hexec⟩ := addScaled_exec p cast.1 t x.2 (n + 3) ac mem _ _ _
      hbase hv' htype (by omega) lc (by omega)
    change ∀ {γ : Type} (k : SemanticAssignment → MemoryState → Tree γ),
      CTree.CreateProg.semanticsDecls scaled.2.decls.reverse ac mem k = k as' mem at hexec
    rw [hexec]
    have bounds := addScaled_ids p cast.1 t x.2 (n + 3)
    change n + 3 ≤ scaled.2.nextId ∧ scaled.1.id < scaled.2.nextId at bounds
    have agree (j) (hj : j < n) := (es j (by omega)).trans (ec j hj)
    apply ih scaled.1 scaled.2.nextId as' vs _ _ (realizes_add hb hi x.2) hs
    · simpa only [SemanticAssignment.getType, agree _ lt] using ht
    · rw [getValues_agree agree (by
        intro h hh; obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hh
        exact lx y (by simp [hy]))]
      exact hvs
    · exact bounds.2
    · omega
    · intro y hy; have := lx y (by simp [hy]); omega
    · intro atail b et hg hb'
      apply hk atail b (fun j hj => (et j (by omega)).trans (agree j hj)) hg
      exact hb'

private def scaledInt (pair : Index × Nat) : Option Int :=
  (signedIndex pair.1).map (· * (pair.2 : Int))

private theorem applyStrides_eq (b : Option Word) (xs : List (Index × Nat)) :
    applyStrides b xs = (do
      let base ← b
      let ns ← xs.mapM scaledInt
      return base + BitVec.ofInt 64 ns.sum) := by
  induction xs generalizing b with
  | nil => cases b <;> simp [applyStrides]
  | cons x xs ih =>
    rw [show applyStrides b (x :: xs) = applyStrides (addWord b x.1 x.2) xs from rfl, ih]
    rcases x with ⟨v, s⟩
    cases b <;> cases v <;> cases he : xs.mapM scaledInt <;>
      simp [List.mapM_cons, he, scaledInt, addWord, indexWord, signedIndex, BitVec.ofInt_add,
        BitVec.ofInt_mul, BitVec.add_assoc]

private def resultPtr (off : Int) : Option Word → Data.LLVM.Ptr
  | none => .poison
  | some w => .val ⟨UInt64.ofBitVec (w + BitVec.ofInt 64 off)⟩

private theorem gep_source (gep : GetelementptrProperties) (p : Data.LLVM.Ptr) (vs : List Index)
    (res : TypeAttr) (m : MemoryState) (off : Int) (ss : Array Nat)
    (hd : gepDecomposition? gep vs.length = some (off, ss))
    (hc : (gep.rawConstantIndices.values.filter (· == -2147483648)).size ≤ vs.length) :
    Llvm.interpretOp' .getelementptr gep #[res] (#[.addr p] ++ (vs.map (.int 64 ·)).toArray)
      #[] m .riscv64 = .ok (#[.addr (resultPtr off (applyStrides (ptrWord p) (vs.zip ss.toList)))], m, none) := by
  have he := interpretGEP_decomposed gep p vs.toArray #[res] m off ss hd hc
  rw [List.map_toArray] at he
  rw [he, applyStrides_eq, Array.mapM_eq_mapM_toList]
  clear he
  simp only [Array.toList_zip, List.toList_toArray]
  have hfun : (fun (v,s) => (signedIndex v).map (· * (s : Int))) = scaledInt := rfl
  rw [hfun]
  cases p <;> cases he : (vs.zip ss.toList).mapM scaledInt <;>
    simp [he, ptrWord, resultPtr, ← List.sum_eq_foldl, pointer_add_offset,
      -UInt64.ofInt_add, Int.add_assoc, BitVec.ofInt_add]
  grind

private abbrev GEPResult := Array RuntimeValue × MemoryState × Option ControlFlowAction
private abbrev gepRel (target source : GEPResult) := OperationResult.isRefinedBy source target

private def returnCreated (ids : Array (Handle OpCode .value)) (a : SemanticAssignment)
    (mem : MemoryState) : Tree GEPResult :=
  match a.getValues ids.toList with
  | some vs => pure (vs.toArray, mem, none)
  | none => fail

private theorem finish_run_append (kind count gep reg res addr n ds) :
    (finishGEP kind count gep reg res addr).run ⟨n, ds⟩ =
      let b := (finishGEP kind count gep reg res addr).run ⟨n, []⟩
      (b.1, ⟨b.2.nextId, b.2.decls ++ ds⟩) := by cases kind <;> rfl

private theorem finishGEP_sim (kind count gep reg res addr n) (a : SemanticAssignment) (m : MemoryState)
    (prop : GetelementptrProperties) (q : LLVM.PointerType) (w : Word) (src : Option Word)
    (off : Int) (ss : Array Nat) (hkind : gepOffsetKind off = kind)
    (hd : gepDecomposition? prop count = some (off, ss)) (hw : realizes src w)
    (hg : a.getProperty gep = some prop) (hr : a.getType reg = some (TypeAttr.of RegisterType {}))
    (hs : a.getType res = some (TypeAttr.of LLVM.PointerType q)) (ha : a.getValue addr = some (.reg ⟨w⟩))
    (lr : reg.id < n) (ls : res.id < n) (la : addr.id < n) :
    let b := (finishGEP kind count gep reg res addr).run ⟨n, []⟩
    _root_.CTree.Sim gepRel (CTree.CreateProg.semanticsDecls b.2.decls.reverse a m (returnCreated b.1.res))
      (pure (#[.addr (resultPtr off src)], m, none) : Tree GEPResult) := by
  cases kind <;>
    simp only [finishGEP, gepOffsetImm, bind, pure, CreateProg.applyNative, CreateProg.operation,
      CreateProg.property, MetadataTuple.fresh, IsMetadataTuple.shape_property, MetadataTuple.Shape.fresh,
      MetadataTuple.Atom.fresh, Array.size_singleton, Array.size_map, Array.size_range, getElem!_pos,
      Array.getElem_map, Array.getElem_range, Nat.zero_lt_one, Nat.add_zero, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.cons_append]
  all_goals
    simp only [SemanticAssignment.getType, SemanticAssignment.getValue, SemanticAssignment.getProperty] at hr hs ha hg
    simp (disch := omega) [CTree.CreateProg.semanticsDecls, CTree.CreateDecl.semantics,
      SemanticAssignment.getTypes, SemanticAssignment.getValues, SemanticAssignment.getProperty,
      SemanticAssignment.getType, SemanticAssignment.getValue, SemanticAssignment.bindProperty,
      SemanticAssignment.bindValues, SemanticAssignment.bindValue, SemanticAssignment.bind,
      MetadataTuple.resolveSemantic, MetadataTuple.Shape.resolveSemantic, MetadataTuple.Atom.resolveSemantic,
      MetadataTuple.bindSemantic, MetadataTuple.Shape.bindSemantic, MetadataTuple.Atom.bindSemantic,
      IsMetadataTuple.shape_property, ite_eq_right, returnCreated, hr, hs, ha, hg, hd,
      CTree.interpretOp', Builtin.interpretOpCTree, Builtin.interpretUnrealizedConversionCastCTree,
      Riscv.interpretOpCTree, Riscv.interpretOp', ctree_semantics, List.range_succ,
      List.getElem?_cons_zero, Attribute.of_def, -Attribute.llvmPointerType_eq_of,
      OperationResult.isRefinedBy, RuntimeValue.isRefinedBy, Data.RISCV.li, Data.RISCV.addi, Data.RISCV.add,
      mkRISCVImm]
    cases src <;> simp_all [resultPtr, realizes]
  case zero.some =>
    unfold gepOffsetKind at hkind
    split at hkind <;> try simp_all
    split at hkind <;> contradiction
  case imm.some =>
    have bounds : -2048 ≤ off ∧ off ≤ 2047 := by
      unfold gepOffsetKind at hkind
      split at hkind <;> try contradiction
      split at hkind <;> simp_all
    have hm : off.bmod (2 ^ 64) = off := Int.bmod_eq_of_le (by omega) (by omega)
    change BitVec.ofInt 64 (((BitVec.ofInt 64 off).setWidth 12).toInt) = BitVec.ofInt 64 off
    apply congrArg (BitVec.ofInt 64)
    rw [← BitVec.signExtend_eq_setWidth_of_le _ (by decide : 12 ≤ 64),
      BitVec.toInt_signExtend_eq_toInt_bmod_of_le _ (by decide), BitVec.toInt_ofInt, hm]
    exact Int.bmod_eq_of_le (by omega) (by omega)

private theorem length_indexIds (n : Nat) (xs : List Nat) : (indexIds n xs).length = xs.length := by
  induction xs generalizing n with
  | nil => rfl
  | cons x xs ih => simp [indexIds, ih]

private theorem scaledLoop_ids (xs : ScaleInputs) (p t n) (hp : p.id < n) :
    n ≤ (scaledLoop xs p t n).2.nextId ∧ (scaledLoop xs p t n).1.id < (scaledLoop xs p t n).2.nextId := by
  induction xs generalizing p n with
  | nil => exact ⟨Nat.le_refl _, hp⟩
  | cons x xs ih =>
    let cast := (castReg x.1 t).run ⟨n, []⟩
    let b := (addScaled p cast.1 t x.2).run ⟨n + 3, []⟩
    have hb := addScaled_ids p cast.1 t x.2 (n + 3)
    change n + 3 ≤ b.2.nextId ∧ b.1.id < b.2.nextId at hb
    have ht := ih b.1 b.2.nextId hb.2
    unfold scaledLoop
    simp only [List.forIn_cons, scaleStep, bind, pure]
    let full := (addScaled p cast.1 t x.2).run ⟨n + 3, cast.2.decls⟩
    change n ≤ ((forIn xs full.1 (scaleStep t)).run full.2).2.nextId ∧
      ((forIn xs full.1 (scaleStep t)).run full.2).1.id < ((forIn xs full.1 (scaleStep t)).run full.2).2.nextId
    dsimp only [full]
    simp only [addScaled_run_append p cast.1 t x.2 (n + 3) cast.2.decls]
    rw [scaleLoop_run_append]
    exact ⟨Nat.le_trans (by omega) ht.1, ht.2⟩

private theorem gep_target (ss : Array Nat) (kind : GEPOffset) (a : SemanticAssignment)
    (m : MemoryState) (p : Data.LLVM.Ptr) (vs : List Index) (prop : GetelementptrProperties)
    (q : LLVM.PointerType) (off : Int) (hd : gepDecomposition? prop ss.size = some (off, ss))
    (hk : gepOffsetKind off = kind)
    (hp : a.getValue ⟨1⟩ = some (.addr p))
    (hg : a.getProperty (opCode := .llvm .getelementptr) ⟨endIndices ss + 3⟩ = some prop)
    (hr : a.getType ⟨endIndices ss⟩ = some (TypeAttr.of LLVM.PointerType q))
    (hi : a.getValues (indexIds 2 ss.toList) = some (vs.map (.int 64 ·))) :
    _root_.CTree.Sim gepRel
      (CTree.CreateProg.semantics (getelementptr_pattern ss kind).creation
        (getelementptr_pattern ss kind).replacement a m)
      (pure (#[.addr (resultPtr off (applyStrides (ptrWord p) (vs.zip ss.toList)))], m, none) : Tree GEPResult) := by
  let n := endIndices ss
  let reg : Handle OpCode .type := ⟨n + 4⟩
  let ar := a.bindType reg (TypeAttr.of RegisterType {})
  let xs := (indexIds 2 ss.toList).zip ss.toList
  let cast := (castReg ⟨1⟩ reg).run ⟨n + 5, []⟩
  let loop := scaledLoop xs ⟨n + 7⟩ reg (n + 8)
  let finish := (finishGEP kind ss.size ⟨n + 3⟩ reg ⟨n⟩ loop.1).run ⟨loop.2.nextId, []⟩
  have hprefix : (prefixGEP n).decls = cast.2.decls ++ [.type (TypeAttr.of RegisterType {}) reg] := rfl
  have loopEq : (forIn xs ⟨n + 7⟩ (scaleStep reg)).run (prefixGEP n) =
      (loop.1, ⟨loop.2.nextId, loop.2.decls ++ (prefixGEP n).decls⟩) :=
    scaleLoop_run_append xs _ reg (n + 8) _
  have he : builtGEP ss kind = (finish.1,
      ⟨finish.2.nextId, finish.2.decls ++ (loop.2.decls ++ (prefixGEP n).decls)⟩) := by
    unfold builtGEP
    simp only [Array.toList_zip, List.toList_toArray]
    change (finishGEP kind ss.size ⟨n + 3⟩ reg ⟨n⟩
      ((forIn xs ⟨n + 7⟩ (scaleStep reg)).run (prefixGEP n)).1).run _ = _
    rw [loopEq]
    exact finish_run_append _ _ _ _ _ _ _ _
  obtain ⟨cd, cr⟩ := gep_creation ss kind
  simp only [CTree.CreateProg.semantics, cd, cr, he, hprefix, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, semanticsDecls_append]
  change _root_.CTree.Sim gepRel (CTree.CreateProg.semanticsDecls cast.2.decls.reverse ar m
    (fun ac m => CTree.CreateProg.semanticsDecls loop.2.decls.reverse ac m
      (fun atail m => CTree.CreateProg.semanticsDecls finish.2.decls.reverse atail m (returnCreated finish.1.res)))) _
  have hn : 2 ≤ n := by dsimp [n, endIndices]; omega
  have hre (j) (hj : j < n + 4) : ar j = a j := by
    simp (disch := omega) [ar, reg, SemanticAssignment.bindType, SemanticAssignment.bind, ite_eq_right]
  have hreg : ar.getType reg = some (TypeAttr.of RegisterType {}) := by
    simp [ar, SemanticAssignment.bindType, SemanticAssignment.bind, SemanticAssignment.getType]
  apply castReg_sim _ _ _ _ _ (.inl p) (by
    simpa only [Sum.elim, SemanticAssignment.getValue, hre 1 (by omega)] using hp) hreg
    (by change 1 < n + 5; omega) (by simp [reg])
  intro ac bits ec hb hb'
  have castId : cast.1 = ⟨n + 7⟩ := by simp [cast, castReg, bind, pure, CreateProg.operation, CreateProg.property]
  change ac.getValue cast.1 = some (.reg ⟨bits⟩) at hb
  rw [castId] at hb
  have regC : ac.getType reg = some (TypeAttr.of RegisterType {}) := by
    simpa only [SemanticAssignment.getType, ec reg.id (by simp [reg])] using hreg
  have oldC (j) (hj : j < n + 4) := (ec j (by omega)).trans (hre j hj)
  have sizes : (indexIds 2 ss.toList).length = ss.toList.length := length_indexIds ..
  have fstEq : xs.map Prod.fst = indexIds 2 ss.toList := List.map_fst_zip (by omega)
  have sndEq : xs.map Prod.snd = ss.toList := List.map_snd_zip (by omega)
  apply scaleLoop_sim xs ⟨n + 7⟩ reg (n + 8) ac m vs bits (ptrWord p) hb' hb regC
  · rw [fstEq, getValues_agree oldC (by
        intro h hm; have hl : h.id < n := indexIds_lt 2 ss.toList _ hm; omega)]
    exact hi
  · simp
  · simp [reg]
  · intro x hm
    have hl : x.1.id < n := indexIds_lt 2 ss.toList _ (List.of_mem_zip hm).1
    omega
  · intro atail w et hw hw'
    rw [sndEq] at hw'
    have old (j) (hj : j < n + 4) := (et j (by omega)).trans (oldC j hj)
    have bounds : n + 8 ≤ loop.2.nextId ∧ loop.1.id < loop.2.nextId := by
      exact scaledLoop_ids xs ⟨n + 7⟩ reg (n + 8) (by simp)
    apply finishGEP_sim kind ss.size _ _ _ _ _ _ _ prop q w _ off ss hk hd hw'
    · simpa only [SemanticAssignment.getProperty, old (n + 3) (by omega)] using hg
    · simpa only [SemanticAssignment.getType, et reg.id (by simp [reg])] using regC
    · simpa only [SemanticAssignment.getType, old n (by omega)] using hr
    · exact hw
    · change n + 4 < loop.2.nextId; omega
    · change n < loop.2.nextId; omega
    · exact bounds.2

/-! ## Values and properties of a successful match -/

private theorem models_append (xs ys : List (MatchDecl OpCode)) (root : Handle OpCode .op)
    (a : SemanticAssignment) (k : SemanticAssignment → Prop) :
    CTree.MatchProg.ModelsDecls root (xs ++ ys) a k =
      CTree.MatchProg.ModelsDecls root xs a (fun b => CTree.MatchProg.ModelsDecls root ys b k) := by
  induction xs generalizing a with
  | nil => rfl
  | cons d xs ih => simp only [List.cons_append, CTree.MatchProg.ModelsDecls, ih]

private theorem modelsIndices (xs : List Nat) (n : Nat) (a : SemanticAssignment) (root : Handle OpCode .op)
    (k : SemanticAssignment → Prop)
    (hk : ∀ b (vs : List Index) (ts : List TypeAttr), (∀ j < n, b j = a j) →
      vs.length = xs.length → ts.length = xs.length →
      b.getValues (indexIds n xs) = some (vs.map (.int 64 ·)) →
      b.getValueTypes (indexIds n xs) = some ts → k b) :
    CTree.MatchProg.ModelsDecls root (indexDecls n xs) a k := by
  induction xs generalizing n a with
  | nil => exact hk a [] [] (by simp) rfl rfl rfl rfl
  | cons x xs ih =>
    simp only [indexDecls, CTree.MatchProg.ModelsDecls, CTree.MatchDecl.Models,
      SemanticAssignment.getType, SemanticAssignment.bindType, SemanticAssignment.bind,
      ↓reduceIte, Option.getD_eq_iff, Option.map_eq_some_iff, IsTypeAttr.cast?_eq_some_iff,
      decide_eq_true_eq, Bool.not_false, Bool.false_eq_true, false_and, or_false,
      exists_and_right, forall_exists_index, and_imp, and_false]
    intro ty it hty hw
    subst ty
    rcases it with ⟨w, sign⟩
    change w = 64 at hw
    subst w
    intro val conform
    obtain ⟨v, rfl⟩ := RuntimeValue.Conforms.integerType.mp conform
    apply ih
    intro b vs ts he hvlen htlen hvs hts
    apply hk b (v :: vs) (TypeAttr.of IntegerType ⟨64, sign⟩ :: ts)
    · intro j hj
      rw [he j (by omega)]
      simp (disch := omega) [SemanticAssignment.bindValue, SemanticAssignment.bind, ite_eq_right]
    · simp [hvlen]
    · simp [htlen]
    · simp only [indexIds, SemanticAssignment.getValues, List.mapM_cons, List.map_cons] at hvs ⊢
      rw [hvs]
      simp [SemanticAssignment.getValue, he (n + 1) (by omega), SemanticAssignment.bindValue,
        SemanticAssignment.bind, hvs]
    · simp only [indexIds, SemanticAssignment.getValueTypes, List.mapM_cons] at hts ⊢
      rw [hts]
      simp [SemanticAssignment.getValueType, he (n + 1) (by omega), SemanticAssignment.bindValue,
        SemanticAssignment.bind, hts]

private theorem getTypes_agree {a a' : SemanticAssignment} {n : Nat} {ids : List (Handle OpCode .value)}
    (he : ∀ j < n, a' j = a j) (hl : ∀ h ∈ ids, h.id < n) :
    a'.getValueTypes ids = a.getValueTypes ids := by
  induction ids with
  | nil => rfl
  | cons h ids ih =>
    simp only [SemanticAssignment.getValueTypes, List.mapM_cons, SemanticAssignment.getValueType,
      he h.id (hl h (by simp))]
    rw [show ids.mapM a'.getValueType = ids.mapM a.getValueType from ih (by grind)]

private theorem gep_models (ss : Array Nat) (kind : GEPOffset) (k : SemanticAssignment → Prop)
    (hk : ∀ a p (vs : List Index) (prop : GetelementptrProperties) (q : LLVM.PointerType) off,
      gepDecomposition? prop ss.size = some (off, ss) → gepOffsetKind off = kind →
      vs.length = ss.size → (prop.rawConstantIndices.values.filter (· == -2147483648)).size ≤ vs.length →
      a.getValue ⟨1⟩ = some (.addr p) → a.getValues (indexIds 2 ss.toList) = some (vs.map (.int 64 ·)) →
      a.getProperty (opCode := .llvm .getelementptr) ⟨endIndices ss + 3⟩ = some prop →
      a.getType ⟨endIndices ss⟩ = some (TypeAttr.of LLVM.PointerType q) → k a) :
    CTree.MatchProg.Models (getelementptr_pattern ss kind).matcher k := by
  rw [CTree.MatchProg.Models, gep_bindingDecls, (gep_matcher_shape ss kind).1]
  simp only [CTree.MatchProg.ModelsDecls, CTree.MatchDecl.Models, SemanticAssignment.getType,
    SemanticAssignment.bindType, SemanticAssignment.bind, ↓reduceIte]
  intro arg _ val hv
  rw [models_append]
  apply modelsIndices
  intro b vs ts he hvl htl hvs hts
  let n := endIndices ss
  have hn : 2 ≤ n := by dsimp [n, endIndices]; omega
  have hp : b.getValue ⟨1⟩ = some val := by
    simp [SemanticAssignment.getValue, he 1 (by decide), SemanticAssignment.bindValue, SemanticAssignment.bind]
  have hpt : b.getValueType ⟨1⟩ = some arg := by
    simp [SemanticAssignment.getValueType, he 1 (by decide), SemanticAssignment.bindValue, SemanticAssignment.bind]
  simp only [CTree.MatchProg.ModelsDecls, CTree.MatchDecl.Models, gepRootDecl, gepGuard]
  intro res _
  let br := b.bindType ⟨n⟩ res
  have ebr (j) (hj : j < n) : br j = b j := by
    simp (disch := omega) [br, SemanticAssignment.bindType, SemanticAssignment.bind, ite_eq_right]
  have idslt : ∀ h ∈ indexIds 2 ss.toList, h.id < n := indexIds_lt 2 ss.toList
  have hrvs := (getValues_agree ebr idslt).trans hvs
  have hrts := (getTypes_agree ebr idslt).trans hts
  have opvals : br.getValues (⟨1⟩ :: indexIds 2 ss.toList) = some (val :: vs.map (.int 64 ·)) := by
    simp only [SemanticAssignment.getValues, List.mapM_cons] at hrvs ⊢
    rw [hrvs]
    simpa [SemanticAssignment.getValue, ebr 1 (by omega), hp] using
      congrArg (fun v => v.bind (fun x => some (x :: vs.map (.int 64 ·)))) hp
  have optys : br.getValueTypes (⟨1⟩ :: indexIds 2 ss.toList) = some (arg :: ts) := by
    simp only [SemanticAssignment.getValueTypes, List.mapM_cons] at hrts ⊢
    rw [hrts]
    simpa [SemanticAssignment.getValueType, ebr 1 (by omega), hpt] using
      congrArg (fun v => v.bind (fun x => some (x :: ts))) hpt
  have resTy : br.getType ⟨n⟩ = some res := by
    simp [br, SemanticAssignment.getType, SemanticAssignment.bindType, SemanticAssignment.bind]
  have resTys : br.getTypes [⟨n⟩] = some [res] := by simp [SemanticAssignment.getTypes, resTy]
  simp only [Array.toList_append, List.toList_toArray, List.cons_append, List.nil_append]
  change (match br.getValues _, br.getValueTypes _, br.getTypes _ with
    | some _, some _, some _ => _ | _, _, _ => False)
  rw [opvals, optys, resTys]
  intro prop _ verified
  let bp := br.bindProperty ⟨n + 3⟩ (opCode := .llvm .getelementptr) prop
  have hprop : bp.getProperty ⟨n + 3⟩ = some prop := by
    simp [bp, SemanticAssignment.getProperty, SemanticAssignment.bindProperty, SemanticAssignment.bind]
  simp only [↓reduceIte, MetadataTuple.resolveSemantic, MetadataTuple.Shape.resolveSemantic,
    MetadataTuple.Atom.resolveSemantic, IsMetadataTuple.shape_property]
  dsimp only [bp, br, n] at hprop
  rw [hprop]
  intro hguard
  cases hd : gepDecomposition? prop ss.size with
  | none => simp [hd] at hguard
  | some pair =>
    obtain ⟨off, strides⟩ := pair
    simp [hd] at hguard
    obtain ⟨rfl, hknd⟩ := hguard
    rw [List.toArray_cons] at verified
    obtain ⟨⟨ptrTy, argType⟩, ⟨q, resType⟩⟩ := gep_pointer_types verified
    have heq : arg = TypeAttr.of LLVM.PointerType ptrTy := Subtype.ext argType
    obtain ⟨p, rfl⟩ := RuntimeValue.Conforms.llvmPointerType.mp (heq ▸ hv)
    have ebp (j) (hj : j < n + 3) : bp j = br j := by
      simp (disch := omega) [bp, SemanticAssignment.bindProperty, SemanticAssignment.bind, ite_eq_right]
    have hres : res = TypeAttr.of LLVM.PointerType q := Subtype.ext resType
    apply hk bp p vs prop q off hd hknd hvl
    · have hc := verified.llvm_gep_dynamic_count
      simp only [Array.size_append, Array.size_singleton, List.size_toArray, List.length_cons, List.length_nil] at hc
      omega
    · simpa only [SemanticAssignment.getValue, ebp 1 (by omega), ebr 1 (by omega)] using hp
    · exact (getValues_agree ebp (by intro h hm; have := idslt h hm; omega)).trans hrvs
    · exact hprop
    · change bp.getType ⟨n⟩ = _
      simpa only [SemanticAssignment.getType, ebp n (by omega), ← hres] using resTy

/-- Every GEP pattern computes the LLVM address using its selected register instructions. -/
theorem getelementptr_pattern_valid (ss : Array Nat) (kind : GEPOffset) :
    CTree.Pattern.Valid (getelementptr_pattern ss kind) := by
  refine ⟨getelementptr_supported ss kind, getelementptr_constrainsRoot ss kind,
    getelementptr_structurallyWellFormed ss kind, ?_⟩
  unfold CTree.Pattern.PreservesSemantics
  apply gep_models
  intro a p vs prop q off hd hk hlen hcount hp hi hg hr m
  have source := gep_source prop p vs (TypeAttr.of LLVM.PointerType q) m off ss (hlen ▸ hd) hcount
  have operands : a.getValues (⟨1⟩ :: indexIds 2 ss.toList) =
      some (.addr p :: vs.map (.int 64 ·)) := by
    simp only [SemanticAssignment.getValues, List.mapM_cons] at hi ⊢
    simp [hp, hi]
  have root : CTree.MatchProg.rootSemantics (getelementptr_pattern ss kind).matcher a m =
      some (pure (#[.addr (resultPtr off (applyStrides (ptrWord p) (vs.zip ss.toList)))], m, none)) := by
    simp only [CTree.MatchProg.rootSemantics, (gep_matcher_shape ss kind).1,
      (gep_matcher_shape ss kind).2, gepRootDecl, ne_eq, not_true_eq_false, ↓reduceIte,
      Array.toList_append, List.toList_toArray, List.cons_append, List.nil_append, operands,
      SemanticAssignment.getTypes, List.mapM_cons, List.mapM_nil, hr, hg, Option.bind_eq_bind,
      Option.bind_some, Option.pure_def]
    simp [CTree.interpretOp', Llvm.interpretOpCTree, ctree_semantics]
    rw [List.toArray_cons (a := RuntimeValue.addr p), source]
    rfl
  rw [root]
  exact gep_target ss kind a m p vs prop q off hd hk hp hg hr hi

end Veir
