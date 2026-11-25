module

public import Veir.PatternRewriter.Puddle.Builders
public import Veir.PatternRewriter.Puddle.Execution

/-!
Scalar ports of `llvm-tic/rules/InstCombineSimplifyRules.td` (Apache-2.0 WITH
LLVM-exception). Rule names and their textual order follow that file. Vector
and floating-point rules are omitted. Comments at the remaining source locations
record missing analyses, representations, effects, or source counterexamples.

Commutative nodes expand into ordered Puddle alternatives, including nested
nodes. Integer literals and constant guards operate on the matched bit width;
repeated constant captures compare bits, while ordinary captures compare SSA
identity. LLVM intrinsic immediate booleans become VeIR properties. One-use
checks are profitability guards, not semantic assumptions. New operations use
only explicitly justified flags; LLVM debug/profile metadata has no counterpart
in these VeIR integer properties. These are executable patterns, not validity
proofs. See the regression tests for supported shapes and boundary cases.
-/

namespace Veir.InstructionSimplify

open Puddle

public section

private def bitwidth (type : TypeAttr) : Nat :=
  match type.val with
  | .integerType t => t.bitwidth
  | _ => 0

private def integerValue (p : LLVMConstantProperties) : Int :=
  match p.value with
  | .integer a => a.value
  | _ => 0

private def isIntegerConstant (p : LLVMConstantProperties) : Bool :=
  match p.value with
  | .integer _ => true
  | _ => false

private def constantBits (type : TypeAttr) (p : LLVMConstantProperties) : BitVec (bitwidth type) :=
  BitVec.ofInt (bitwidth type) (integerValue p)

private def constantIs (value : Int) (p : LLVMConstantProperties) : Bool :=
  match p.value with
  | .integer a => BitVec.ofInt a.type.bitwidth a.value == BitVec.ofInt a.type.bitwidth value
  | _ => false

private def constantExtreme (minimum : Bool) (p : LLVMConstantProperties) : Bool :=
  match p.value with
  | .integer a =>
    BitVec.ofInt a.type.bitwidth a.value ==
      (if minimum then BitVec.intMin a.type.bitwidth else BitVec.intMax a.type.bitwidth)
  | _ => false

private def integerConstant (type : TypeAttr) (value : Int) : LLVMConstantProperties :=
  { value := .integer (IntegerAttr.ofInt value ((type.cast? IntegerType).getD (IntegerType.signless 1))) }

private def isPowerOfTwo (n : Nat) : Bool :=
  n != 0 && n &&& (n - 1) == 0

private def byteSwap (x : BitVec w) : BitVec w :=
  match Data.LLVM.Int.bswap (.val x) with
  | .val result => result
  | _ => 0

/-- Count operand uses, including two uses in the same instruction. -/
private def requireUses (op : Handle OpCode .op) (count : Nat) : MatchProg.Builder Unit := do
  let () ← MatchProg.inspectOperation (Outputs := Unit) op fun ctx ptr => do
    let mut use := (ptr.getResult 0).getFirstUse! ctx
    for _ in [:count] do
      let some u := use | none
      use := u.getNextUse! ctx
    guard use.isNone

private def requireEitherOperandOneUse (root : Handle OpCode .op) : MatchProg.Builder Unit := do
  let () ← MatchProg.inspectOperation (Outputs := Unit) root fun ctx op => do
    guard ((op.getOperands! ctx).any fun v =>
      (v.getFirstUse! ctx).any fun u => (u.getNextUse! ctx).isNone)

private def orient (swaps index : Nat) (a b : Handle OpCode .value) :
    Array (Handle OpCode .value) :=
  if swaps.testBit index then #[b, a] else #[a, b]

/-- Compile once, retaining the authored orientation before its alternatives. -/
private def compileVariants (commutativeNodes : Nat) (pattern : Nat → Pattern OpCode) :
    Array (CompiledPattern OpCode) :=
  (Array.range (2 ^ commutativeNodes)).map fun swaps => (pattern swaps).compile

/-- A field path is a prefix when it selects a containing subaggregate. -/
private def positionPrefix (a b : Array Int) : Bool :=
  a.size ≤ b.size && a == b.extract 0 a.size

set_option linter.unusedVariables false

-- InstCombineSimplifyRules.td:165
/-- Zero-length memory intrinsics have no accesses, including volatile ones. -/
def erase_zero_length_memory_intrinsic : Array (CompiledPattern OpCode) :=
  #[Llvm.intr__memcpy, Llvm.intr__memmove, Llvm.intr__memset].map fun opcode =>
    (Pattern.Builder
      (do
        let pointerType ← MatchProg.type (Attr := LLVM.PointerType)
        let destination ← MatchProg.value pointerType
        let source ← MatchProg.value (← MatchProg.type (Attr := TypeAttr))
        let lengthType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
        let length ← MatchProg.operation (.llvm .mlir__constant) #[] #[lengthType] (constantIs 0)
        let _ ← MatchProg.root (.llvm opcode) #[destination, source, length.res[0]!] #[]
        return ())
      pure
      (fun _ => (#[] : Array (Handle OpCode .value)))).compile

-- erase_invalid_length_#AtomicMemory.rule_id_component (InstCombineSimplifyRules.td:177): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- erase_store_of_value_loaded_from_same_address (InstCombineSimplifyRules.td:194): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `store_is_unordered`); these are not available in this root-replacement port.

-- erase_repeated_identical_local_store (InstCombineSimplifyRules.td:207): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `store_is_simple`); these are not available in this root-replacement port.

-- erase_unordered_store_to_constant_memory (InstCombineSimplifyRules.td:224): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `store_is_unordered`); these are not available in this root-replacement port.

-- canonicalize_poison_store_unreachable_region (InstCombineSimplifyRules.td:233): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- canonicalize_undef_pointer_store_unreachable_region (InstCombineSimplifyRules.td:248): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- rebase_dead_retyped_constant_alloca_transfer_before_erasure (InstCombineSimplifyRules.td:280): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- erase_dead_alloca_derived_write_graph (InstCombineSimplifyRules.td:296): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- fold_non_escaping_alloca_equality_comparisons (InstCombineSimplifyRules.td:307): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- erase_transfer_safe_instructions_before_unreachable (InstCombineSimplifyRules.td:320): not ported.
-- Requires TIC effect `erase_transfer_safe_unreachable_prefix` and its analysis/property
-- contract; this is not a supported root-value replacement.

-- canonicalize_ # Operation # _uniform_phi_pair (InstCombineSimplifyRules.td:325): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- canonicalize_ # Operation # _swapped_select_pair (InstCombineSimplifyRules.td:330): not ported.
-- Family requires TIC descriptor `canonicalize_commutative_binop_root_pair`, whose contextual
-- matching/effects have no VeIR equivalent.

-- canonicalize_commutative_intrinsic_uniform_phi_pair (InstCombineSimplifyRules.td:338): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- canonicalize_commutative_intrinsic_swapped_select_pair (InstCombineSimplifyRules.td:342): not ported.
-- Requires inherited TIC descriptor `canonicalize_commutative_intrinsic_root_pair`; its
-- contextual matching/effects have no VeIR equivalent.

-- fold_undefined_freeze_with_user_consensus (InstCombineSimplifyRules.td:431): not ported.
-- Requires use-graph/dominance facts and coordinated sharing of an undef choice; a root-local
-- replacement cannot implement that policy.

-- lower_false_assume (InstCombineSimplifyRules.td:448): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- lower_undef_or_poison_assume (InstCombineSimplifyRules.td:455): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- evaluate_object_size_intrinsic (InstCombineSimplifyRules.td:466): not ported.
-- Requires TIC effect `evaluate_object_size` and its analysis/property contract; this is not a
-- supported root-value replacement.

-- infer_memory_intrinsic_destination_alignment (InstCombineSimplifyRules.td:474): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_memory_intrinsic_is_nonvolatile`); these are not available in this root-
-- replacement port.

-- scalarize_constant_memcpy (InstCombineSimplifyRules.td:482): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `power_of_2`); these are not available in this root-replacement port.

-- scalarize_single_access_memcpy (InstCombineSimplifyRules.td:495): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `power_of_2`); these are not available in this root-replacement port.

-- memcpy_same_source_and_destination (InstCombineSimplifyRules.td:514): not ported.
-- VeIR memory intrinsics have no per-call memory_effects_none property; this is an effect update,
-- not a value replacement.

-- memcpy_source_addrspacecast_of_destination_is_noop (InstCombineSimplifyRules.td:523): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates; these
-- are not available in this root-replacement port.

-- memmove_source_addrspacecast_of_destination_is_noop (InstCombineSimplifyRules.td:525): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates; these
-- are not available in this root-replacement port.

-- erase_#Transfer.rule_id_component#_from_never_initialized_alloca (InstCombineSimplifyRules.td:533): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- zero_initialized_allocation_memcpy_to_memset (InstCombineSimplifyRules.td:542): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- zero_initialized_allocation_memmove_to_memset (InstCombineSimplifyRules.td:544): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- memcpy_to_unmodifiable_destination (InstCombineSimplifyRules.td:549): not ported.
-- VeIR memory intrinsics have no per-call memory_effects_none property; this is an effect update,
-- not a value replacement.

-- memset_to_unmodifiable_destination (InstCombineSimplifyRules.td:554): not ported.
-- VeIR memory intrinsics have no per-call memory_effects_none property; this is an effect update,
-- not a value replacement.

-- memset_undef_or_poison_value (InstCombineSimplifyRules.td:561): not ported.
-- VeIR memory intrinsics have no per-call memory_effects_none property; this is an effect update,
-- not a value replacement.

-- scalarize_constant_memset (InstCombineSimplifyRules.td:568): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `power_of_2`); these are not available in this root-replacement port.

-- scalarize_constant_element_atomic_memset (InstCombineSimplifyRules.td:582): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `power_of_2`); these are not available in this root-replacement port.

-- scalarize_single_access_#AtomicTransfer.rule_id_component (InstCombineSimplifyRules.td:601): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `power_of_2`); these are not available in this root-replacement port.

-- erase_same_source_and_destination_#AtomicTransfer.rule_id_component (InstCombineSimplifyRules.td:628): not ported.
-- Family requires contextual descriptors/effects `AtomicTransfer`, `erase_root`; no corresponding
-- VeIR matcher/effect interface is available.

-- fold_add_of_#Splice.rule_id_component (InstCombineSimplifyRules.td:741): not ported.
-- Family requires TIC descriptor `binop_of_vector_splice`, whose contextual matching/effects have
-- no VeIR equivalent.

-- InstCombineSimplifyRules.td:794
def reconstruct_two_element_aggregate : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun _ => Pattern.Builder
    (do
      let aggregateType ← MatchProg.type (Attr := TypeAttr) fun t =>
        match t.val with
        | .llvmArrayType a => a.size == 2
        | .llvmStructType s => s.body.size == 2
        | _ => false
      let firstType ← MatchProg.type (Attr := TypeAttr)
      let secondType ← MatchProg.type (Attr := TypeAttr)
      let aggregate ← MatchProg.value aggregateType
      let undef ← MatchProg.operation (.llvm .mlir__undef) #[] #[aggregateType]
      let first ← MatchProg.operation (.llvm .extractvalue) #[aggregate] #[firstType]
        (fun p => p.position.values == #[0])
      let second ← MatchProg.operation (.llvm .extractvalue) #[aggregate] #[secondType]
        (fun p => p.position.values == #[1])
      let insertion ← MatchProg.operation (.llvm .insertvalue) #[undef.res[0]!, first.res[0]!] #[aggregateType]
        (fun p => p.position.values == #[0])
      let _ ← MatchProg.root (.llvm .insertvalue) #[insertion.res[0]!, second.res[0]!] #[aggregateType]
        (fun p => p.position.values == #[1])
      return aggregate)
    pure
    (fun aggregate => aggregate)

-- InstCombineSimplifyRules.td:813
def extract_value_from_identical_aggregate_insert_path : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun _ => Pattern.Builder
    (do
      let aggregateType ← MatchProg.type (Attr := TypeAttr)
      let insertedType ← MatchProg.type (Attr := TypeAttr)
      let aggregate ← MatchProg.value aggregateType
      let inserted ← MatchProg.value insertedType
      let insertion ← MatchProg.operation (.llvm .insertvalue) #[aggregate, inserted] #[aggregateType]
      let extraction ← MatchProg.root (.llvm .extractvalue) #[insertion.res[0]!] #[insertedType]
      let () ← MatchProg.matchNative (extraction.properties, insertion.properties) fun (ep, ip) =>
        ep.position.values == ip.position.values
      return inserted)
    pure
    (fun inserted => inserted)

-- InstCombineSimplifyRules.td:821
def extract_prefix_of_aggregate_insert_path : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun _ => Pattern.Builder
    (do
      let aggregateType ← MatchProg.type (Attr := TypeAttr)
      let insertedType ← MatchProg.type (Attr := TypeAttr)
      let resultType ← MatchProg.type (Attr := TypeAttr)
      let aggregate ← MatchProg.value aggregateType
      let inserted ← MatchProg.value insertedType
      let insertion ← MatchProg.operation (.llvm .insertvalue) #[aggregate, inserted] #[aggregateType]
      let extraction ← MatchProg.root (.llvm .extractvalue) #[insertion.res[0]!] #[resultType]
      let () ← MatchProg.matchNative (extraction.properties, insertion.properties) fun (ep, ip) =>
        positionPrefix ep.position.values ip.position.values && ep.position.values.size < ip.position.values.size
      return (resultType, aggregate, inserted, extraction.properties, insertion.properties))
    (fun (resultType, aggregate, inserted, ep, ip) => do
      let projected ← CreateProg.operation (.llvm .extractvalue) #[aggregate] #[resultType] (.inr ep)
      let suffix ← CreateProg.applyNative (ep, ip) fun (ep, ip) =>
        some ({ position := { ip.position with values := ip.position.values.extract ep.position.values.size } } : LLVMPositionProperties)
      let result ← CreateProg.operation (.llvm .insertvalue) #[projected.res[0]!, inserted] #[resultType] (.inr suffix)
      return result.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:831
def aggregate_insert_path_prefix_of_extract : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun _ => Pattern.Builder
    (do
      let aggregateType ← MatchProg.type (Attr := TypeAttr)
      let insertedType ← MatchProg.type (Attr := TypeAttr)
      let resultType ← MatchProg.type (Attr := TypeAttr)
      let aggregate ← MatchProg.value aggregateType
      let inserted ← MatchProg.value insertedType
      let insertion ← MatchProg.operation (.llvm .insertvalue) #[aggregate, inserted] #[aggregateType]
      let extraction ← MatchProg.root (.llvm .extractvalue) #[insertion.res[0]!] #[resultType]
      let () ← MatchProg.matchNative (extraction.properties, insertion.properties) fun (ep, ip) =>
        positionPrefix ip.position.values ep.position.values && ip.position.values.size < ep.position.values.size
      return (resultType, aggregate, inserted, extraction.properties, insertion.properties))
    (fun (resultType, aggregate, inserted, ep, ip) => do
      let suffix ← CreateProg.applyNative (ep, ip) fun (ep, ip) =>
        some ({ position := { ep.position with values := ep.position.values.extract ip.position.values.size } } : LLVMPositionProperties)
      let result ← CreateProg.operation (.llvm .extractvalue) #[inserted] #[resultType] (.inr suffix)
      return result.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:844
def bypass_aggregate_insert_on_diverging_extract_path : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun _ => Pattern.Builder
    (do
      let aggregateType ← MatchProg.type (Attr := TypeAttr)
      let insertedType ← MatchProg.type (Attr := TypeAttr)
      let resultType ← MatchProg.type (Attr := TypeAttr)
      let aggregate ← MatchProg.value aggregateType
      let inserted ← MatchProg.value insertedType
      let insertion ← MatchProg.operation (.llvm .insertvalue) #[aggregate, inserted] #[aggregateType]
      let extraction ← MatchProg.root (.llvm .extractvalue) #[insertion.res[0]!] #[resultType]
      let () ← MatchProg.matchNative (extraction.properties, insertion.properties) fun (ep, ip) =>
        !positionPrefix ip.position.values ep.position.values && !positionPrefix ep.position.values ip.position.values
      return (resultType, aggregate, inserted, extraction.properties, insertion.properties))
    (fun (resultType, aggregate, inserted, ep, ip) => do
      let result ← CreateProg.operation (.llvm .extractvalue) #[aggregate] #[resultType] (.inr ep)
      return result.res[0]!)
    (fun result => result)

-- remove_overwritten_aggregate_insert (InstCombineSimplifyRules.td:855): not ported.
-- Requires scanning an arbitrary single-use aggregate insertion chain for a later covering
-- overwrite; this root-local port does not perform that use-graph analysis.

-- strengthen_memory_transfer_source_alignment (InstCombineSimplifyRules.td:864): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_memory_intrinsic_is_nonvolatile`); these are not available in this root-
-- replacement port.

-- scalarize_single_access_memmove (InstCombineSimplifyRules.td:876): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `power_of_2`); these are not available in this root-replacement port.

-- memmove_same_source_and_destination (InstCombineSimplifyRules.td:892): not ported.
-- VeIR memory intrinsics have no per-call memory_effects_none property; this is an effect update,
-- not a value replacement.

-- memmove_to_unmodifiable_destination (InstCombineSimplifyRules.td:896): not ported.
-- VeIR memory intrinsics have no per-call memory_effects_none property; this is an effect update,
-- not a value replacement.

-- memmove_from_constant_global_to_memcpy (InstCombineSimplifyRules.td:903): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `is_constant_global`); these are not available in this root-replacement port.

-- element_atomic_memmove_from_constant_global_to_memcpy (InstCombineSimplifyRules.td:916): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `is_constant_global`); these are not available in this root-replacement port.

-- invalid_null_memory_intrinsic_destination_requires_zero_length (InstCombineSimplifyRules.td:931): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_memory_intrinsic_is_nonvolatile`); these are not available in this root-
-- replacement port.

-- invalid_null_memory_transfer_source_requires_zero_length (InstCombineSimplifyRules.td:946): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_memory_intrinsic_is_nonvolatile`); these are not available in this root-
-- replacement port.

-- null_callee_call_is_unreachable (InstCombineSimplifyRules.td:957): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- null_callee_call_result_is_poison (InstCombineSimplifyRules.td:965): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- undef_callee_call_is_unreachable (InstCombineSimplifyRules.td:977): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- undef_callee_call_result_is_poison (InstCombineSimplifyRules.td:984): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- null_callee_invoke_result_is_poison (InstCombineSimplifyRules.td:997): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- undef_callee_invoke_result_is_poison (InstCombineSimplifyRules.td:1006): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- unused_removable_allocation_invoke_to_donothing (InstCombineSimplifyRules.td:1019): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_call_result_with_returned_argument (InstCombineSimplifyRules.td:1029): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- order_commutative_intrinsic_operands (InstCombineSimplifyRules.td:1037): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- enforce_constant_source_alignment_for_read_only_alloca_#Transfer.rule_id_component (InstCombineSimplifyRules.td:1990): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_undef_read_only_alloca_zero_memcpy_with_constant_source (InstCombineSimplifyRules.td:2005): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_undef_read_only_alloca_zero_memmove_with_constant_source (InstCombineSimplifyRules.td:2008): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_casted_same_type_read_only_alloca_memcpy_with_constant_source (InstCombineSimplifyRules.td:2015): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_casted_same_type_read_only_alloca_memmove_with_constant_source (InstCombineSimplifyRules.td:2018): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_closed_retyped_read_only_alloca_memcpy_with_constant_source (InstCombineSimplifyRules.td:2021): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_closed_retyped_read_only_alloca_memmove_with_constant_source (InstCombineSimplifyRules.td:2024): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_same_type_read_only_alloca_memcpy_with_casted_constant_source (InstCombineSimplifyRules.td:2031): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_same_type_read_only_alloca_memmove_with_casted_constant_source (InstCombineSimplifyRules.td:2034): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_same_type_read_only_alloca_memcpy_with_constant_source (InstCombineSimplifyRules.td:2037): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_same_type_read_only_alloca_memmove_with_constant_source (InstCombineSimplifyRules.td:2039): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_read_only_alloca_memcpy_with_addrspacecast_constant_source (InstCombineSimplifyRules.td:2045): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_read_only_alloca_memmove_with_addrspacecast_constant_source (InstCombineSimplifyRules.td:2048): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_read_only_alloca_memcpy_with_constant_source (InstCombineSimplifyRules.td:2055): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_read_only_alloca_memmove_with_constant_source (InstCombineSimplifyRules.td:2057): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_masked_read_only_alloca_memcpy_with_constant_source (InstCombineSimplifyRules.td:2067): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- replace_masked_read_only_alloca_memmove_with_constant_source (InstCombineSimplifyRules.td:2069): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- forward_same_block_available_load (InstCombineSimplifyRules.td:2808): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_unordered`); these are not available in this root-replacement port.

-- split_one_element_struct_load (InstCombineSimplifyRules.td:2846): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_simple`); these are not available in this root-replacement port.

-- split_two_element_stride_struct_load (InstCombineSimplifyRules.td:2867): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- split_padding_free_struct_load_fields (InstCombineSimplifyRules.td:2903): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_simple`); these are not available in this root-replacement port.

-- split_bounded_array_load_fields (InstCombineSimplifyRules.td:2915): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_simple`); these are not available in this root-replacement port.

-- split_padding_free_struct_store_fields (InstCombineSimplifyRules.td:2933): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_simple`); these are not available in this root-replacement port.

-- split_bounded_array_store_fields (InstCombineSimplifyRules.td:2947): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_simple`); these are not available in this root-replacement port.

-- load_extract_first_aggregate_element (InstCombineSimplifyRules.td:2964): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_simple`); these are not available in this root-replacement port.

-- store_two_values_from_complete_array (InstCombineSimplifyRules.td:3017): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates; these
-- are not available in this root-replacement port.

-- store_two_values_from_complete_stride_struct (InstCombineSimplifyRules.td:3024): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `all_of`); these are not available in this root-replacement port.

-- load_proves_first_nonzero_gep_index_zero_for_all_uses (InstCombineSimplifyRules.td:3051): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- store_proves_first_nonzero_gep_index_zero_for_all_uses (InstCombineSimplifyRules.td:3064): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- load_proves_first_nonzero_gep_index_zero (InstCombineSimplifyRules.td:3076): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- store_proves_first_nonzero_gep_index_zero (InstCombineSimplifyRules.td:3082): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- load_of_select_to_select_of_safe_loads (InstCombineSimplifyRules.td:3092): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_unordered`); these are not available in this root-replacement port.

-- load_of_addrspacecast_select_to_select_of_safe_loads (InstCombineSimplifyRules.td:3123): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_unordered`); these are not available in this root-replacement port.

-- load_protected_field_pointer (InstCombineSimplifyRules.td:3165): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `load_is_unordered`); these are not available in this root-replacement port.

-- store_protected_field_pointer (InstCombineSimplifyRules.td:3188): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_unordered`); these are not available in this root-replacement port.

-- fold_alloca_constant_array_size (InstCombineSimplifyRules.td:3215): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- canonicalize_alloca_array_size_index_type (InstCombineSimplifyRules.td:3224): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- canonicalize_unit_alloca_array_size (InstCombineSimplifyRules.td:3235): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- alloca_poison_array_size_to_poison (InstCombineSimplifyRules.td:3246): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- merge_zero_sized_alloca_with_entry_alloca (InstCombineSimplifyRules.td:3255): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- move_first_zero_sized_alloca_to_entry (InstCombineSimplifyRules.td:3268): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- canonicalize_byte_constant_store_value (InstCombineSimplifyRules.td:3284): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates; these
-- are not available in this root-replacement port.

-- store_consume_bitcast_value (InstCombineSimplifyRules.td:3290): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `store_can_consume_bitcast`); these are not available in this root-replacement port.

-- erase_preceding_overwritten_unordered_store (InstCombineSimplifyRules.td:3301): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `store_is_unordered`); these are not available in this root-replacement port.

-- erase_undef_store_to_defined_pointer (InstCombineSimplifyRules.td:3323): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_unordered`); these are not available in this root-replacement port.

-- erase_poison_store_to_defined_pointer (InstCombineSimplifyRules.td:3336): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_unordered`); these are not available in this root-replacement port.

-- store_to_undefined_null_uses_poison_value (InstCombineSimplifyRules.td:3348): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_unordered`); these are not available in this root-replacement port.

-- store_dereference_removes_false_null_select (InstCombineSimplifyRules.td:3360): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_unordered`); these are not available in this root-replacement port.

-- store_dereference_removes_true_null_select (InstCombineSimplifyRules.td:3372): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_store_is_unordered`); these are not available in this root-replacement port.

-- load_dereference_removes_false_null_select (InstCombineSimplifyRules.td:3387): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `null_pointer_is_undefined`); these are not available in this root-replacement port.

-- load_dereference_removes_true_null_select (InstCombineSimplifyRules.td:3393): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `null_pointer_is_undefined`); these are not available in this root-replacement port.

-- store_dereference_removes_null_select_from_gep_base (InstCombineSimplifyRules.td:3399): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- store_dereference_removes_null_select_from_gep_base_commuted (InstCombineSimplifyRules.td:3413): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- load_from_undefined_null_is_unreachable (InstCombineSimplifyRules.td:3432): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- observed_nonnull_removes_private_false_null_select (InstCombineSimplifyRules.td:3454): not ported.
-- Requires inherited TIC descriptor `observed_nonnull_removes_private_null_select`; its
-- contextual matching/effects have no VeIR equivalent.

-- observed_nonnull_removes_private_true_null_select (InstCombineSimplifyRules.td:3458): not ported.
-- Requires inherited TIC descriptor `observed_nonnull_removes_private_null_select`; its
-- contextual matching/effects have no VeIR equivalent.

-- observed_nonnull_removes_private_gep_false_null_select (InstCombineSimplifyRules.td:3482): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- observed_nonnull_removes_private_gep_true_null_select (InstCombineSimplifyRules.td:3488): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- load_dereference_removes_null_select_from_gep_base (InstCombineSimplifyRules.td:3499): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- load_dereference_removes_null_select_from_gep_chain2 (InstCombineSimplifyRules.td:3512): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- load_dereference_removes_null_select_from_gep_chain3 (InstCombineSimplifyRules.td:3526): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- load_dereference_removes_null_select_from_gep_base_phi (InstCombineSimplifyRules.td:3545): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- load_from_undef_or_poison_pointer_is_unreachable (InstCombineSimplifyRules.td:3563): not ported.
-- Requires LLVM's non-terminating UB marker and/or unreachable-region surgery, outside Puddle's
-- root-replacement model.

-- load_from_uninitialized_alloca_is_undef (InstCombineSimplifyRules.td:3577): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- load_from_write_free_zero_initialized_allocation (InstCombineSimplifyRules.td:3586): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- load_through_gep_from_write_free_undef_initialized_allocation_is_undef (InstCombineSimplifyRules.td:3601): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- infer_known_nonnull_call_arguments (InstCombineSimplifyRules.td:3617): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `root_is_not_object_size_query`); these are not available in this root-replacement
-- port.

-- infer_known_nonnull_invoke_arguments (InstCombineSimplifyRules.td:3634): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_threadlocal_address_return_alignment (InstCombineSimplifyRules.td:3643): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_call_nounwind_from_caller (InstCombineSimplifyRules.td:3651): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_inline_asm_call_nounwind (InstCombineSimplifyRules.td:3658): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_inline_asm_invoke_nounwind (InstCombineSimplifyRules.td:3665): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- remove_redundant_convergent_call_site (InstCombineSimplifyRules.td:3672): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_printf_format_argument_attributes (InstCombineSimplifyRules.td:3676): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_strlen_string_argument_attributes (InstCombineSimplifyRules.td:3681): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_strcmp_lhs_access_attributes (InstCombineSimplifyRules.td:3686): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_strcmp_rhs_access_attributes (InstCombineSimplifyRules.td:3688): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_memcmp_lhs_access_attributes (InstCombineSimplifyRules.td:3691): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_memcmp_rhs_access_attributes (InstCombineSimplifyRules.td:3693): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_strnlen_string_access_attributes (InstCombineSimplifyRules.td:3696): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_memchr_access_attributes (InstCombineSimplifyRules.td:3698): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_memrchr_access_attributes (InstCombineSimplifyRules.td:3700): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_infer_memintrinsic_argument_access_attributes (InstCombineSimplifyRules.td:3703): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates; these
-- are not available in this root-replacement port.

-- infer_nonnull_destination_i_element_atomic_memset (InstCombineSimplifyRules.td:3708): not ported.
-- Requires LLVM memory-access/alias/ordering analysis or access metadata and graph updates
-- (notably `known_non_zero`); these are not available in this root-replacement port.

-- infer_nonnull_destination_#AtomicTransfer.rule_id_component (InstCombineSimplifyRules.td:3716): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_nonnull_source_#AtomicTransfer.rule_id_component (InstCombineSimplifyRules.td:3728): not ported.
-- Requires LLVM call-site/library attributes, intrinsic schemas, or invoke effects that VeIR does
-- not model through a corresponding Puddle interface.

-- infer_call_allocation_result_attributes (InstCombineSimplifyRules.td:3734): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- infer_invoke_allocation_result_attributes (InstCombineSimplifyRules.td:3738): not ported.
-- Requires allocation escape/initialization analysis or rewriting the allocation's users; neither
-- contract is exposed to these Puddle patterns.

-- ptrtoint_wider_than_native_width (InstCombineSimplifyRules.td:3743): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- ptrtoint_narrower_than_native_width (InstCombineSimplifyRules.td:3749): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- inttoptr_native_width (InstCombineSimplifyRules.td:3755): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- inttoptr_add_of_ptrtoint_to_byte_gep (InstCombineSimplifyRules.td:3766): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- ptrtoint_one_use_null_gep (InstCombineSimplifyRules.td:3783): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep2 (InstCombineSimplifyRules.td:3791): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep3 (InstCombineSimplifyRules.td:3793): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep4 (InstCombineSimplifyRules.td:3795): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep5 (InstCombineSimplifyRules.td:3797): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep_chain2 (InstCombineSimplifyRules.td:3800): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep_chain3_nuw (InstCombineSimplifyRules.td:3810): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep_chain3 (InstCombineSimplifyRules.td:3816): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_null_gep_narrow_index (InstCombineSimplifyRules.td:3824): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- ptrtoint_one_use_gep_from_inttoptr_nuw (InstCombineSimplifyRules.td:3835): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_gep_from_inttoptr (InstCombineSimplifyRules.td:3842): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_gep_chain2_from_inttoptr_nuw (InstCombineSimplifyRules.td:3852): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_gep_chain2_from_inttoptr (InstCombineSimplifyRules.td:3859): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoint_one_use_ptrmask (InstCombineSimplifyRules.td:3869): not ported.
-- VeIR has no llvm.ptrmask operation or pointer-mask property/analysis interface.

-- ptrtoaddr_one_use_ptrmask (InstCombineSimplifyRules.td:3878): not ported.
-- VeIR has no llvm.ptrmask operation or pointer-mask property/analysis interface.

-- ptrtoaddr_one_use_null_gep (InstCombineSimplifyRules.td:3887): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- ptrtoaddr_one_use_gep_from_inttoptr_nuw (InstCombineSimplifyRules.td:3897): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- ptrtoaddr_one_use_gep_from_inttoptr (InstCombineSimplifyRules.td:3904): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_sub_pointer_observations_rewrite_address_users (InstCombineSimplifyRules.td:3914): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- icmp_#Cmp#_ptrtoint_pair (InstCombineSimplifyRules.td:3927): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- icmp_#Cmp#_inttoptr_ptrtoint_roundtrip (InstCombineSimplifyRules.td:3958): not ported.
-- Family requires contextual descriptors/effects `Cmp`, `replace_root_operand`; no corresponding
-- VeIR matcher/effect interface is available.

-- icmp_#Cmp#_inttoptr_null (InstCombineSimplifyRules.td:3968): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- icmp_#Cmp#_native_inttoptr_pair (InstCombineSimplifyRules.td:3974): not ported.
-- Family requires contextual descriptors/effects `Cmp`; no corresponding VeIR matcher/effect
-- interface is available.

-- icmp_#Cmp#_native_inttoptr_constant (InstCombineSimplifyRules.td:3984): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- icmp_#Cmp#_ptrtoint_zero (InstCombineSimplifyRules.td:4002): not ported.
-- Family requires contextual descriptors/effects `Cmp`; no corresponding VeIR matcher/effect
-- interface is available.

-- sub_gep_base_root_nuw_nusw (InstCombineSimplifyRules.td:4014): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_base_#Policy.tag (InstCombineSimplifyRules.td:4022): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_base_native (InstCombineSimplifyRules.td:4030): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep_inbounds (InstCombineSimplifyRules.td:4045): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep_#Policy.tag (InstCombineSimplifyRules.td:4054): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep_native (InstCombineSimplifyRules.td:4062): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- return_sub_gep_base_#Policy.tag (InstCombineSimplifyRules.td:4080): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- return_sub_gep_base_native (InstCombineSimplifyRules.td:4096): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep2_base_root_nuw_nusw (InstCombineSimplifyRules.td:4115): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep2_base_#Policy.tag (InstCombineSimplifyRules.td:4123): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep2_base_native (InstCombineSimplifyRules.td:4131): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep2_inbounds (InstCombineSimplifyRules.td:4143): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep2_#Policy.tag (InstCombineSimplifyRules.td:4152): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep2_native (InstCombineSimplifyRules.td:4160): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_chain2_base_nusw (InstCombineSimplifyRules.td:4174): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_chain2_base_native (InstCombineSimplifyRules.td:4185): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep_chain2_nusw (InstCombineSimplifyRules.td:4197): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_base_gep_chain2_native (InstCombineSimplifyRules.td:4208): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_chain2_common_link_native (InstCombineSimplifyRules.td:4225): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_chain2_gep_native (InstCombineSimplifyRules.td:4245): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_gep_chain2_native (InstCombineSimplifyRules.td:4260): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_rewrite_left_shared_chain2_gep_difference_inbounds (InstCombineSimplifyRules.td:4281): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- sub_rewrite_right_shared_chain2_gep_difference_inbounds (InstCombineSimplifyRules.td:4286): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- sub_rewrite_left_shared_chain2_gep_difference_nuw (InstCombineSimplifyRules.td:4291): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- sub_rewrite_right_shared_chain2_gep_difference_nuw (InstCombineSimplifyRules.td:4296): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- sub_rewrite_right_shared_prefixed_chain2_gep_difference_plain (InstCombineSimplifyRules.td:4301): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- sub_two_geps_nusw (InstCombineSimplifyRules.td:4304): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_two_geps_native (InstCombineSimplifyRules.td:4316): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_gep_constant_gep_inbounds_native (InstCombineSimplifyRules.td:4336): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_two_gep2_nusw (InstCombineSimplifyRules.td:4351): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- sub_two_gep2_native (InstCombineSimplifyRules.td:4363): not ported.
-- Requires target/address-space pointer representation and index-width contracts. Existing GEP
-- lowering is RV64-specific; this pass has no target data-layout parameter.

-- InstCombineSimplifyRules.td:4383
def select_poison_cond : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr) (fun t => t.isa IntegerType || t.isa LLVM.PointerType)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let op2 ← MatchProg.operation (.llvm .mlir__poison) #[] #[t1]
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, x3, y4] #[t0]
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .mlir__poison) #[] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4398
def nsw_mul_neg_one : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op1 ← MatchProg.root (.llvm .mul) (orient swaps 0 x2 op3.res[0]!) #[t0] (fun p => p.nsw)
      return (t0, x2))
    (fun (t0, x2) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      let new4 ← CreateProg.operation (.llvm .sub) #[k5.res[0]!, x2] #[t0] (.inl { nsw := true, nuw := false })
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4402
def mul_neg_one : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op1 ← MatchProg.root (.llvm .mul) (orient swaps 0 x2 op3.res[0]!) #[t0]
      let () ← MatchProg.matchNative op1.properties fun m0 => ((!m0.nsw))
      return (t0, x2, op1))
    (fun (t0, x2, op1) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (op1.properties, t0) fun (m0, m1) => some (integerConstant m1 (BitVec.ofInt (bitwidth m1) (0)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      let new4 ← CreateProg.operation (.llvm .sub) #[k5.res[0]!, x2] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4408
def sdiv_neg_one : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op1 ← MatchProg.root (.llvm .sdiv) #[x2, op3.res[0]!] #[t0]
      return (t0, x2))
    (fun (t0, x2) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      let new4 ← CreateProg.operation (.llvm .sub) #[k5.res[0]!, x2] #[t0] (.inl { nsw := true, nuw := false })
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4413
def srem_neg_one : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op1 ← MatchProg.root (.llvm .srem) #[x2, op3.res[0]!] #[t0]
      return (t0, x2))
    (fun (t0, x2) => do
      let k4Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k4 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k4Props)
      return k4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4424
def and_two_same_masks_drop_one : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y6 ← MatchProg.value t0
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 1 y6 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .and) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      return (t0, x3, y6, op4))
    (fun (t0, x3, y6, op4) => do
      let new9 ← CreateProg.operation (.llvm .and) #[y6, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .and) #[x3, new9.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4434
def or_not_and3_contains : Array (CompiledPattern OpCode) :=
  compileVariants 4 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 0 x2 y6) #[t0]
      let z7 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .and) (orient swaps 1 op5.res[0]! z7) #[t0]
      let op8 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op3 ← MatchProg.operation (.llvm .xor) (orient swaps 2 op4.res[0]! op8.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .or) (orient swaps 3 x2 op3.res[0]!) #[t0]
      return (t0, x2, y6, z7))
    (fun (t0, x2, y6, z7) => do
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (-1)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      return k9.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4438
def or_not_and4_contains : Array (CompiledPattern OpCode) :=
  compileVariants 5 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let y7 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .and) (orient swaps 0 x2 y7) #[t0]
      let z8 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 1 op6.res[0]! z8) #[t0]
      let q9 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .and) (orient swaps 2 op5.res[0]! q9) #[t0]
      let op10 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op3 ← MatchProg.operation (.llvm .xor) (orient swaps 3 op4.res[0]! op10.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .or) (orient swaps 4 x2 op3.res[0]!) #[t0]
      return (t0, x2, y7, z8, q9))
    (fun (t0, x2, y7, z8, q9) => do
      let k11Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (-1)).toInt)
      let k11 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k11Props)
      return k11.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4443
def and_not_or3_contains : Array (CompiledPattern OpCode) :=
  compileVariants 4 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .or) (orient swaps 0 x2 y6) #[t0]
      let z7 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .or) (orient swaps 1 op5.res[0]! z7) #[t0]
      let op8 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op3 ← MatchProg.operation (.llvm .xor) (orient swaps 2 op4.res[0]! op8.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .and) (orient swaps 3 x2 op3.res[0]!) #[t0]
      return (t0, x2, y6, z7))
    (fun (t0, x2, y6, z7) => do
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      return k9.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4447
def and_not_or4_contains : Array (CompiledPattern OpCode) :=
  compileVariants 5 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let y7 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .or) (orient swaps 0 x2 y7) #[t0]
      let z8 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .or) (orient swaps 1 op6.res[0]! z8) #[t0]
      let q9 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .or) (orient swaps 2 op5.res[0]! q9) #[t0]
      let op10 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op3 ← MatchProg.operation (.llvm .xor) (orient swaps 3 op4.res[0]! op10.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .and) (orient swaps 4 x2 op3.res[0]!) #[t0]
      return (t0, x2, y7, z8, q9))
    (fun (t0, x2, y7, z8, q9) => do
      let k11Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k11 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k11Props)
      return k11.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4452
def select_true : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr) (fun t => t.isa IntegerType || t.isa LLVM.PointerType)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let op2 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] (constantIs (1))
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, x3, y4] #[t0]
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:4457
def select_false : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr) (fun t => t.isa IntegerType || t.isa LLVM.PointerType)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let op2 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] (constantIs (0))
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, x3, y4] #[t0]
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      return y4)
    (fun result => result)

-- InstCombineSimplifyRules.td:4462
def select_same : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr) (fun t => t.isa IntegerType || t.isa LLVM.PointerType)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c2 ← MatchProg.value t1
      let x3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .select) #[c2, x3, x3] #[t0]
      return (t0, t1, c2, x3))
    (fun (t0, t1, c2, x3) => do
      return x3)
    (fun result => result)

-- canonicalize_icmp_ne_with_invertible_users (InstCombineSimplifyRules.td:4471): not ported.
-- Requires coordinated inversion of the comparison and its users; Puddle replaces only the
-- matched root.

-- InstCombineSimplifyRules.td:4493
def add_i1_to_xor : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let y3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .add) (orient swaps 0 x2 y3) #[t0]
      return (t0, x2, y3))
    (fun (t0, x2, y3) => do
      let new4 ← CreateProg.operation (.llvm .xor) #[x2, y3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4500
def sub_i1_to_xor : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let y3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .sub) #[x2, y3] #[t0]
      return (t0, x2, y3))
    (fun (t0, x2, y3) => do
      let new4 ← CreateProg.operation (.llvm .xor) #[y3, x2] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4505
def mul_i1_to_and : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let y3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .mul) (orient swaps 0 x2 y3) #[t0]
      return (t0, x2, y3))
    (fun (t0, x2, y3) => do
      let new4 ← CreateProg.operation (.llvm .and) #[x2, y3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4514
def select_true_false : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op1 ← MatchProg.root (.llvm .select) #[c2, op3.res[0]!, op4.res[0]!] #[t0]
      return (t0, c2))
    (fun (t0, c2) => do
      return c2)
    (fun result => result)

-- select_logical_and_keep_condition_when_it_implies_rhs (InstCombineSimplifyRules.td:4519): not ported.
-- Requires LLVM boolean implication and poison-speculation facts, which VeIR does not currently
-- compute.

-- select_logical_or_keep_condition_when_false_implies_rhs_false (InstCombineSimplifyRules.td:4524): not ported.
-- Requires LLVM boolean implication and poison-speculation facts, which VeIR does not currently
-- compute.

-- select_logical_and_keep_#P#_rhs_when_rhs_implies_condition (InstCombineSimplifyRules.td:4537): not ported.
-- Requires LLVM boolean implication and poison-speculation facts, which VeIR does not currently
-- compute.

-- select_logical_or_keep_#P#_rhs_when_rhs_false_implies_condition_false (InstCombineSimplifyRules.td:4550): not ported.
-- Requires LLVM boolean implication and poison-speculation facts, which VeIR does not currently
-- compute.

-- bitwise_and_keep_rhs_when_rhs_implies_lhs (InstCombineSimplifyRules.td:4567): not ported.
-- Requires LLVM boolean implication and poison-speculation facts, which VeIR does not currently
-- compute.

-- bitwise_or_keep_rhs_when_rhs_false_implies_lhs_false (InstCombineSimplifyRules.td:4574): not ported.
-- Requires LLVM boolean implication and poison-speculation facts, which VeIR does not currently
-- compute.

-- InstCombineSimplifyRules.td:4582
def umax_shl_nuw_scale_inc : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .shl) #[x3, op4.res[0]!] #[t5] (fun p => p.nuw)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] (constantIs (1))
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op6.res[0]!) #[t5]
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t5]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => (((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (0))))
      return (t5, x3, op2, op4))
    (fun (t5, x3, op2, op4) => do
      let t4 ← CreateProg.type (IntegerType.signless 1)
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k9Props)
      let new8 ← CreateProg.operation (.llvm .icmp) #[x3, k9.res[0]!] #[t4] (.inl { predicate := .eq })
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (1)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k10Props)
      let new7 ← CreateProg.operation (.llvm .select) #[new8.res[0]!, k10.res[0]!, op2.res[0]!] #[t5]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4590
-- Same scalar pattern as `umax_shl_nuw_scale_inc`; keep the source rule name.
def umax_shl_nuw_scale_inc_commuted : Array (CompiledPattern OpCode) := umax_shl_nuw_scale_inc

-- InstCombineSimplifyRules.td:4598
def umax_mul_nuw_scale_inc : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .mul) (orient swaps 0 x3 op4.res[0]!) #[t5] (fun p => p.nuw)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] (constantIs (1))
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 x3 op6.res[0]!) #[t5]
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t5]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => (((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (0))) && ((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (1))))
      return (t5, x3, op2, op4))
    (fun (t5, x3, op2, op4) => do
      let t4 ← CreateProg.type (IntegerType.signless 1)
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k9Props)
      let new8 ← CreateProg.operation (.llvm .icmp) #[x3, k9.res[0]!] #[t4] (.inl { predicate := .eq })
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (1)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k10Props)
      let new7 ← CreateProg.operation (.llvm .select) #[new8.res[0]!, k10.res[0]!, op2.res[0]!] #[t5]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4608
-- Same scalar pattern as `umax_mul_nuw_scale_inc`; keep the source rule name.
def umax_mul_nuw_scale_inc_commuted : Array (CompiledPattern OpCode) := umax_mul_nuw_scale_inc

-- InstCombineSimplifyRules.td:4622
def umin_i1 : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let y3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 x2 y3) #[t0]
      return (t0, x2, y3))
    (fun (t0, x2, y3) => do
      let new4 ← CreateProg.operation (.llvm .and) #[x2, y3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4622
def umax_i1 : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let y3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 0 x2 y3) #[t0]
      return (t0, x2, y3))
    (fun (t0, x2, y3) => do
      let new4 ← CreateProg.operation (.llvm .or) #[x2, y3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4622
def smin_i1 : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let y3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 0 x2 y3) #[t0]
      return (t0, x2, y3))
    (fun (t0, x2, y3) => do
      let new4 ← CreateProg.operation (.llvm .or) #[x2, y3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4622
def smax_i1 : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let y3 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 0 x2 y3) #[t0]
      return (t0, x2, y3))
    (fun (t0, x2, y3) => do
      let new4 ← CreateProg.operation (.llvm .and) #[x2, y3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4627
def select_eq_zero_self : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.predicate == .eq)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, x3] #[t0]
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:4632
def select_ne_zero_self : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.predicate == .ne)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, x3, op5.res[0]!] #[t0]
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      return x3)
    (fun result => result)

-- canonicalize_icmp_eq_and1_one_with_invertible_users (InstCombineSimplifyRules.td:4643): not ported.
-- Requires coordinated inversion of the comparison and its users; Puddle replaces only the
-- matched root.

-- InstCombineSimplifyRules.td:4653
def shl_oob_poison : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .shl) #[x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat ≥ (bitwidth m0))))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      let new4 ← CreateProg.operation (.llvm .mlir__poison) #[] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4653
def lshr_oob_poison : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .lshr) #[x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat ≥ (bitwidth m0))))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      let new4 ← CreateProg.operation (.llvm .mlir__poison) #[] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4653
def ashr_oob_poison : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .ashr) #[x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat ≥ (bitwidth m0))))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      let new4 ← CreateProg.operation (.llvm .mlir__poison) #[] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4662
def select_sgt_const_and_to_and_smin : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m1) == ((constantBits m0 m2) &&& (constantBits m0 m3))))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .and) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4675
def select_sgt_negative_const_xor_signbit_to_and_smin : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .xor) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op7.properties, op5.properties) fun (m0, m1, m2, m3) => ((decide ((constantBits m0 m1).toInt < 0)) && ((constantBits m0 m2) == BitVec.intMin (bitwidth m0)) && ((constantBits m0 m3) == (((constantBits m0 m1) + (BitVec.ofInt (bitwidth m0) (1))) &&& (~~~(constantBits m0 m2)))))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op7.properties, op5.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 ((constantBits m0 m1) + (BitVec.ofInt (bitwidth m0) (1))).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k10Props)
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, k10.res[0]!] #[t0]
      let k11Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op7.properties, op5.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 (~~~(constantBits m0 m2)).toInt)
      let k11 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k11Props)
      let new8 ← CreateProg.operation (.llvm .and) #[new9.res[0]!, k11.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4692
def select_ult_and_const_to_and_umin : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ult)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op6.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t0, op7.properties, op4.properties, op6.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m1) == ((constantBits m0 m2) &&& (constantBits m0 m3))))
      return (t0, t1, x3, op4, op6, op7))
    (fun (t0, t1, x3, op4, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .and) #[new9.res[0]!, op6.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4705
def select_sgt_nsw_add_const_to_smax_nsw_add : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op6.res[0]!) #[t0] (fun p => p.nsw)
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t0, op7.properties, op4.properties, op6.properties, op5.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) + (constantBits m0 m3))) && (m4.nsw) && (decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ∧ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)))
      return (t0, t1, x3, op5, op4, op6, op7))
    (fun (t0, t1, x3, op5, op4, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op6.res[0]!] #[t0] (.inl { nsw := true, nuw := false })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4721
def select_slt_nsw_add_const_to_smin_nsw_add : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .slt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op6.res[0]!) #[t0] (fun p => p.nsw)
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t0, op7.properties, op4.properties, op6.properties, op5.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) + (constantBits m0 m3))) && (m4.nsw) && (decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ∧ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)))
      return (t0, t1, x3, op5, op4, op6, op7))
    (fun (t0, t1, x3, op5, op4, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op6.res[0]!] #[t0] (.inl { nsw := true, nuw := false })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4733
def select_sgt_add_const_to_smax_add : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .add) #[x3, op6.res[0]!] #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m2) == (constantBits m0 m1) + (constantBits m0 m3)))
      return (t0, t1, x3, op4, op6, op7))
    (fun (t0, t1, x3, op4, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op6.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4747
def select_slt_add_const_to_smin_add : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .slt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .add) #[x3, op6.res[0]!] #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m2) == (constantBits m0 m1) + (constantBits m0 m3)))
      return (t0, t1, x3, op4, op6, op7))
    (fun (t0, t1, x3, op4, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op6.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4757
def select_ult_add_const_to_umin_add : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ult)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .add) #[x3, op6.res[0]!] #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m2) == (constantBits m0 m1) + (constantBits m0 m3)))
      return (t0, t1, x3, op4, op6, op7))
    (fun (t0, t1, x3, op4, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op6.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4767
def select_ugt_add_const_to_umax_add : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ugt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .add) #[x3, op6.res[0]!] #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m2) == (constantBits m0 m1) + (constantBits m0 m3)))
      return (t0, t1, x3, op4, op6, op7))
    (fun (t0, t1, x3, op4, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op6.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4778
def select_sgt_const_nsw_nuw_add_to_smin_nsw_nuw_add : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op7.res[0]!) #[t0] (fun p => p.nsw && p.nuw)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) + (constantBits m0 m3))) && (m4.nsw) && (m4.nuw) && (decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ∧ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)) && (decide (((constantBits m0 m2).toNat + (constantBits m0 m3).toNat) < 2 ^ (bitwidth m0))))
      return (t0, t1, x3, op6, op4, op5, op7))
    (fun (t0, t1, x3, op6, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op7.res[0]!] #[t0] (.inl { nsw := true, nuw := true })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4794
def select_sgt_const_nsw_nuw_add_to_smin_nuw_add : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op7.res[0]!) #[t0] (fun p => p.nsw && p.nuw)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) + (constantBits m0 m3))) && (m4.nsw) && (m4.nuw) && (decide (((constantBits m0 m2).toNat + (constantBits m0 m3).toNat) < 2 ^ (bitwidth m0))))
      return (t0, t1, x3, op6, op4, op5, op7))
    (fun (t0, t1, x3, op6, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op7.res[0]!] #[t0] (.inl { nsw := false, nuw := true })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4809
def select_sgt_const_nsw_nuw_add_to_smin_nsw_add : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op7.res[0]!) #[t0] (fun p => p.nsw && p.nuw)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) + (constantBits m0 m3))) && (m4.nsw) && (m4.nuw) && (decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ∧ ((constantBits m0 m2).toInt + (constantBits m0 m3).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)))
      return (t0, t1, x3, op6, op4, op5, op7))
    (fun (t0, t1, x3, op6, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op7.res[0]!] #[t0] (.inl { nsw := true, nuw := false })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4823
def select_sgt_const_add_to_smin_add : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .add) #[x3, op7.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m2) == (constantBits m0 m1) + (constantBits m0 m3)))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4833
def select_ugt_const_add_to_umin_add : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ugt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .add) #[x3, op7.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m2) == (constantBits m0 m1) + (constantBits m0 m3)))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- select_ult_const_add_to_decremented_umax_add (InstCombineSimplifyRules.td:4843): not ported.
-- Source counterexample (i8): X=Bound=Selected=0, Addend=1 gives 1 before and 0 after; Bound-1
-- wraps.

-- InstCombineSimplifyRules.td:4855
def select_ugt_const_mul_to_umin_mul : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ugt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .mul) #[x3, op7.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m1) == ((constantBits m0 m2) * (constantBits m0 m3))))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .mul) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- select_sgt_const_mul_to_incremented_smin_mul (InstCombineSimplifyRules.td:4863): not ported.
-- Source counterexample (i8): X=0, Bound=127, Factor=1, Selected=-128 gives 0 before and -128
-- after; Bound+1 wraps.

-- InstCombineSimplifyRules.td:4872
def select_ult_const_nsw_nuw_mul_to_umax_nsw_nuw_mul : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ult)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .mul) (orient swaps 0 x3 op7.res[0]!) #[t0] (fun p => p.nsw && p.nuw)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) * (constantBits m0 m3))) && (m4.nsw) && (m4.nuw) && (decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m2).toInt * (constantBits m0 m3).toInt) ∧ ((constantBits m0 m2).toInt * (constantBits m0 m3).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)) && (decide (((constantBits m0 m2).toNat * (constantBits m0 m3).toNat) < 2 ^ (bitwidth m0))))
      return (t0, t1, x3, op6, op4, op5, op7))
    (fun (t0, t1, x3, op6, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .mul) #[new9.res[0]!, op7.res[0]!] #[t0] (.inl { nsw := true, nuw := true })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4889
def select_ult_const_nsw_nuw_mul_to_umax_nuw_mul : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ult)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .mul) (orient swaps 0 x3 op7.res[0]!) #[t0] (fun p => p.nsw && p.nuw)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) * (constantBits m0 m3))) && (m4.nsw) && (m4.nuw) && (decide (((constantBits m0 m2).toNat * (constantBits m0 m3).toNat) < 2 ^ (bitwidth m0))))
      return (t0, t1, x3, op6, op4, op5, op7))
    (fun (t0, t1, x3, op6, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .mul) #[new9.res[0]!, op7.res[0]!] #[t0] (.inl { nsw := false, nuw := true })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4905
def select_ult_const_nsw_nuw_mul_to_umax_nsw_mul : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ult)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .mul) (orient swaps 0 x3 op7.res[0]!) #[t0] (fun p => p.nsw && p.nuw)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties, op6.properties) fun (m0, m1, m2, m3, m4) => (((constantBits m0 m1) == ((constantBits m0 m2) * (constantBits m0 m3))) && (m4.nsw) && (m4.nuw) && (decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m2).toInt * (constantBits m0 m3).toInt) ∧ ((constantBits m0 m2).toInt * (constantBits m0 m3).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)))
      return (t0, t1, x3, op6, op4, op5, op7))
    (fun (t0, t1, x3, op6, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .mul) #[new9.res[0]!, op7.res[0]!] #[t0] (.inl { nsw := true, nuw := false })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4922
def add_nsw_smin_saturation_bound_to_sadd_sat : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .add) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0] (fun p => p.nsw)
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt > 0)) && ((constantBits m0 m2) == ((BitVec.intMax (bitwidth m0)) - (constantBits m0 m1))))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let new6 ← CreateProg.operation (.llvm .intr__sadd__sat) #[x3, op5.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4932
def or_smax_adjacent_equal_endpoints_raise_bound : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .or) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => (((constantBits m0 m1) != BitVec.intMax (bitwidth m0)) && (((constantBits m0 m1) ||| (constantBits m0 m2)) == (((constantBits m0 m1) + (BitVec.ofInt (bitwidth m0) (1))) ||| (constantBits m0 m2))))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 ((constantBits m0 m1) + (BitVec.ofInt (bitwidth m0) (1))).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k8Props)
      let new7 ← CreateProg.operation (.llvm .intr__smax) #[x3, k8.res[0]!] #[t0]
      let new6 ← CreateProg.operation (.llvm .or) #[new7.res[0]!, op5.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4953
def select_slt_const_or_to_or_smax : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .slt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .or) #[x3, op7.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m1) == ((constantBits m0 m2) ||| (constantBits m0 m3))))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .or) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4964
def select_ugt_const_smin_to_smin_umin : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ugt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op5.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt >= (BitVec.ofInt (bitwidth m0) (0)).toInt)) && (decide ((constantBits m0 m2).toInt >= (BitVec.ofInt (bitwidth m0) (0)).toInt)) && (decide ((constantBits m0 m2).toNat <= (constantBits m0 m1).toNat)))
      return (t0, t1, x3, op5, op4))
    (fun (t0, t1, x3, op5, op4) => do
      let new7 ← CreateProg.operation (.llvm .intr__umin) #[x3, op5.res[0]!] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4975
def select_ugt_const_smax_to_smax_umin : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ugt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m1) == (constantBits m0 m2)) && (decide ((constantBits m0 m2).toInt >= (constantBits m0 m3).toInt)))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__smax) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4985
def select_slt_const_umin_to_umin_smax : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .slt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m1) == (constantBits m0 m2)) && (decide ((constantBits m0 m2).toNat <= (constantBits m0 m3).toNat)))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:4995
def select_sgt_const_umax_to_umax_smin : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties, op7.properties) fun (m0, m1, m2, m3) => (((constantBits m0 m1) == (constantBits m0 m2)) && (decide ((constantBits m0 m2).toNat >= (constantBits m0 m3).toNat)))
      return (t0, t1, x3, op4, op5, op7))
    (fun (t0, t1, x3, op4, op5, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__umax) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5046
def correlated_signed_clamp_lower_less : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .slt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (op4.properties, op5.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op7.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt <= (constantBits m0 m2).toInt)))
      return (t0, t1, x3, op4, op7))
    (fun (t0, t1, x3, op4, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__smin) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5046
def correlated_signed_clamp_lower_greater : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op6.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op4.properties, op6.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt <= (constantBits m0 m2).toInt)))
      return (t0, t1, x3, op4, op6))
    (fun (t0, t1, x3, op4, op6) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__smin) #[new9.res[0]!, op6.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5046
def correlated_signed_clamp_upper_greater : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (op4.properties, op5.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op7.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt <= (constantBits m0 m2).toInt)))
      return (t0, t1, x3, op4, op7))
    (fun (t0, t1, x3, op4, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op7.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__smin) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5046
def correlated_signed_clamp_upper_less : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .slt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op6.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op6.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt <= (constantBits m0 m2).toInt)))
      return (t0, t1, x3, op4, op6))
    (fun (t0, t1, x3, op4, op6) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, op6.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__smin) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5051
def correlated_unsigned_clamp_lower_less : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ult)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (op4.properties, op5.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op7.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat <= (constantBits m0 m2).toNat)))
      return (t0, t1, x3, op4, op7))
    (fun (t0, t1, x3, op4, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[new9.res[0]!, op7.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5051
def correlated_unsigned_clamp_lower_greater : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ugt)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op6.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op4.properties, op6.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat <= (constantBits m0 m2).toNat)))
      return (t0, t1, x3, op4, op6))
    (fun (t0, t1, x3, op4, op6) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op4.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[new9.res[0]!, op6.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5051
def correlated_unsigned_clamp_upper_greater : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ugt)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op6 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 0 x3 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op6.res[0]!] #[t0]
      let () ← MatchProg.matchNative (op4.properties, op5.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← requireUses op6.op 1
      let () ← MatchProg.matchNative (t0, op7.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat <= (constantBits m0 m2).toNat)))
      return (t0, t1, x3, op4, op7))
    (fun (t0, t1, x3, op4, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op7.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5051
def correlated_unsigned_clamp_upper_less : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) #[x3, op4.res[0]!] #[t1] (fun p => p.predicate == .ult)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 0 x3 op6.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, op7.res[0]!] #[t0]
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op6.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat <= (constantBits m0 m2).toNat)))
      return (t0, t1, x3, op4, op6))
    (fun (t0, t1, x3, op4, op6) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, op6.res[0]!] #[t0]
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- add_udiv_remainder_bit_to_unsigned_divceil (InstCombineSimplifyRules.td:5061): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- add_zext_udiv_remainder_bit_to_unsigned_divceil (InstCombineSimplifyRules.td:5074): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- map_#Rotate.rule_id_component#_over_one_use_select (InstCombineSimplifyRules.td:5091): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_aggregate_extract_over_select (InstCombineSimplifyRules.td:5106): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_#Predicate#_over_constant_and_common_select_arms (InstCombineSimplifyRules.td:5120): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_#Predicate#_over_one_use_nonboolean_select_with_constant (InstCombineSimplifyRules.td:5165): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_#Operation.tag#_over_one_use_select (InstCombineSimplifyRules.td:5174): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_ctpop_over_one_use_select (InstCombineSimplifyRules.td:5176): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_#Operation.tag#_lhs_over_one_use_select (InstCombineSimplifyRules.td:5184): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_#Operation.tag#_rhs_over_one_use_select (InstCombineSimplifyRules.td:5186): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_uadd_with_overflow_lhs_over_one_use_select (InstCombineSimplifyRules.td:5209): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_and_over_one_use_nonboolean_select_with_constant (InstCombineSimplifyRules.td:5215): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_mul_lhs_over_one_use_select_when_both_arms_simplify (InstCombineSimplifyRules.td:5222): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- map_ashr_rhs_over_one_use_select_when_both_arms_simplify (InstCombineSimplifyRules.td:5228): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- InstCombineSimplifyRules.td:5256
def xor_one_use_select_constant_zero_same_constant_true : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t6 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let cond3 ← MatchProg.value t6
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .select) #[cond3, op4.res[0]!, op5.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .xor) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, t6, cond3, op4, op2))
    (fun (t0, t6, cond3, op4, op2) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .select) #[cond3, k7.res[0]!, op4.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5267
def xor_one_use_select_zero_constant_same_constant_false : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t6 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let cond3 ← MatchProg.value t6
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .select) #[cond3, op4.res[0]!, op5.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .xor) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, t6, cond3, op5, op2))
    (fun (t0, t6, cond3, op5, op2) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .select) #[cond3, op5.res[0]!, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- map_#Predicate#_over_aligned_selects (InstCombineSimplifyRules.td:5279): not ported.
-- Requires TIC's select-arm simplification query and clone policy; Puddle has no branch-local
-- simplifier.

-- InstCombineSimplifyRules.td:5324
def bswap_bswap : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bswap) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      return (t0, x3))
    (fun (t0, x3) => do
      return x3)
    (fun result => result)

-- bswap_one_use_shl_byte_aligned (InstCombineSimplifyRules.td:5333): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- bswap_one_use_lshr_byte_aligned (InstCombineSimplifyRules.td:5338): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- InstCombineSimplifyRules.td:5346
def bswap_shl_to_single_low_byte : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .shl) #[x3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => (((constantBits m0 m1) == ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (8)))))
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) 255).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .and) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5351
def bswap_lshr_to_single_high_byte : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .lshr) #[x3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => (((constantBits m0 m1) == ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (8)))))
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 (byteSwap (BitVec.ofNat (bitwidth m0) 255)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .and) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5361
def bswap_shl_leaving_one_byte_to_lshr : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .shl) #[x3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat ≥ (bitwidth m0) - 8 ∧ (constantBits m0 m1).toNat < (bitwidth m0))))
      return (t0, x3, op2, op4))
    (fun (t0, x3, op2, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (8))).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .lshr) #[op2.res[0]!, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5368
def bswap_lshr_leaving_one_byte_to_shl : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .lshr) #[x3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat ≥ (bitwidth m0) - 8 ∧ (constantBits m0 m1).toNat < (bitwidth m0))))
      return (t0, x3, op2, op4))
    (fun (t0, x3, op2, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (8))).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .shl) #[op2.res[0]!, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5377
def bswap_and_low_byte_to_shl : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (255))
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3))
    (fun (t0, x3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (8))).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .shl) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5381
def bswap_and_high_byte_to_lshr : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => (((constantBits m0 m1) == ((BitVec.ofInt (bitwidth m0) (-1)) <<< ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (8))).toNat)))
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (8))).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .lshr) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5395
def bswap_trunc_bswap_to_high_bytes : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t4 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t4
      let op3 ← MatchProg.operation (.llvm .intr__bswap) #[x4] #[t4]
      let op2 ← MatchProg.operation (.llvm .trunc) #[op3.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      let () ← MatchProg.matchNative (t4, t0) fun (m0, m1) => (true && (decide ((bitwidth m0) > (bitwidth m1))))
      return (t0, t4, x4, op2))
    (fun (t0, t4, x4, op2) => do
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t4, t0) fun (m0, m1) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t4] (.inr k8Props)
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t4, t0) fun (m0, m1) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (bitwidth m1)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t4] (.inr k9Props)
      let new7 ← CreateProg.operation (.llvm .sub) #[k8.res[0]!, k9.res[0]!] #[t4]
      let new6 ← CreateProg.operation (.llvm .lshr) #[x4, new7.res[0]!] #[t4]
      let new5 ← CreateProg.operation (.llvm .trunc) #[new6.res[0]!] #[t0] (.inl { nsw := false, nuw := true })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5410
def select_eq_zero_add_identity : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.predicate == .eq)
      let y5 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .add) (orient swaps 1 y5 x3) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, y5, op6.res[0]!] #[t0]
      return (t0, t1, x3, y5))
    (fun (t0, t1, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .add) #[y5, x3] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- narrow_truncated_smax_smin_sext_constants_at_call (InstCombineSimplifyRules.td:5422): not ported.
-- Requires TIC effect `replace_truncating_users_and_erase`, `erase_root` and its
-- analysis/property contract; this is not a supported root-value replacement.

-- InstCombineSimplifyRules.td:5448
def xor_pair_common_operand_cancel : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let c4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .xor) (orient swaps 0 a3 c4) #[t0]
      let b6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .xor) (orient swaps 1 b6 c4) #[t0]
      let op1 ← MatchProg.root (.llvm .xor) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, a3, c4, b6))
    (fun (t0, a3, c4, b6) => do
      let new7 ← CreateProg.operation (.llvm .xor) #[a3, b6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- umin_known_unsigned_upper_bound (InstCombineSimplifyRules.td:5459): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- umin_known_unsigned_lower_bound (InstCombineSimplifyRules.td:5468): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- sadd_sat_no_signed_or_unsigned_overflow_to_add (InstCombineSimplifyRules.td:5481): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- sadd_sat_no_signed_overflow_to_add (InstCombineSimplifyRules.td:5488): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- uadd_sat_no_unsigned_overflow_to_add (InstCombineSimplifyRules.td:5496): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- usub_sat_no_unsigned_overflow_to_sub (InstCombineSimplifyRules.td:5501): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- ssub_sat_no_signed_overflow_to_sub (InstCombineSimplifyRules.td:5506): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- uadd_sat_always_overflows_to_max (InstCombineSimplifyRules.td:5515): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- usub_sat_always_overflows_to_zero (InstCombineSimplifyRules.td:5520): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- sadd_sat_always_overflows_low_to_min (InstCombineSimplifyRules.td:5525): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- sadd_sat_always_overflows_high_to_max (InstCombineSimplifyRules.td:5533): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- ssub_sat_always_overflows_low_to_min (InstCombineSimplifyRules.td:5541): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- ssub_sat_always_overflows_high_to_max (InstCombineSimplifyRules.td:5549): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- InstCombineSimplifyRules.td:5561
def uadd_sat_nested_constants : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__uadd__sat) #[x3, op4.res[0]!] #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__uadd__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide (((constantBits m0 m1).toNat + (constantBits m0 m2).toNat) < 2 ^ (bitwidth m0))))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 ((constantBits m0 m1) + (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__uadd__sat) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5568
def uadd_sat_nested_constants_to_max : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__uadd__sat) #[x3, op4.res[0]!] #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__uadd__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((!(decide (((constantBits m0 m1).toNat + (constantBits m0 m2).toNat) < 2 ^ (bitwidth m0)))))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (-1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      return k6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5575
def usub_sat_nested_constants : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__usub__sat) #[x3, op4.res[0]!] #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__usub__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide (((constantBits m0 m1).toNat + (constantBits m0 m2).toNat) < 2 ^ (bitwidth m0))))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 ((constantBits m0 m1) + (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__usub__sat) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5582
def usub_sat_nested_constants_to_zero : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__usub__sat) #[x3, op4.res[0]!] #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__usub__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((!(decide (((constantBits m0 m1).toNat + (constantBits m0 m2).toNat) < 2 ^ (bitwidth m0)))))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      return k6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5589
def sadd_sat_nested_same_sign_constants : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__sadd__sat) #[x3, op4.res[0]!] #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__sadd__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((((decide ((constantBits m0 m1).toInt >= 0)) && (decide ((constantBits m0 m2).toInt >= 0))) || ((decide ((constantBits m0 m1).toInt < 0)) && (decide ((constantBits m0 m2).toInt < 0)))) && (decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m1).toInt + (constantBits m0 m2).toInt) ∧ ((constantBits m0 m1).toInt + (constantBits m0 m2).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 ((constantBits m0 m1) + (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__sadd__sat) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5604
def usub_sat_nuw_add_constant_lanes : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op4.res[0]!) #[t0] (fun p => p.nuw)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__usub__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat ≥ (constantBits m0 m2).toNat)))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 ((constantBits m0 m1) - (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .add) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5614
def select_eq_pick_rhs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 y4) #[t1] (fun p => p.predicate == .eq)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, x3, y4] #[t0]
      let () ← MatchProg.matchNative () fun () => (true)
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      return y4)
    (fun result => result)

-- InstCombineSimplifyRules.td:5620
def select_ne_pick_lhs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 y4) #[t1] (fun p => p.predicate == .ne)
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, y4, x3] #[t0]
      let () ← MatchProg.matchNative () fun () => (true)
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      return y4)
    (fun result => result)

-- fshr_self_const_to_fshl (InstCombineSimplifyRules.td:5628): not ported.
-- Source counterexample with APInt arithmetic (i3): X=1, C=4 rotates right to 4, but (3-4)%3
-- wraps to 1 and rotates left to 2.

-- InstCombineSimplifyRules.td:5640
def smax_smin_val : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 0 x2 op3.res[0]!) #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => (((constantBits m0 m1) == BitVec.intMin (bitwidth m0)))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      return x2)
    (fun result => result)

-- InstCombineSimplifyRules.td:5646
def smin_smax_val : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 0 x2 op3.res[0]!) #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => (((constantBits m0 m1) == BitVec.intMax (bitwidth m0)))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      return x2)
    (fun result => result)

-- InstCombineSimplifyRules.td:5652
def smin_smin_val : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 0 x2 op3.res[0]!) #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => (((constantBits m0 m1) == BitVec.intMin (bitwidth m0)))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      return op3.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5658
def smax_smax_val : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 0 x2 op3.res[0]!) #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => (((constantBits m0 m1) == BitVec.intMax (bitwidth m0)))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      return op3.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:5669
def select_cond_cond_false : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op1 ← MatchProg.root (.llvm .select) #[c2, c2, op3.res[0]!] #[t0]
      return (t0, c2))
    (fun (t0, c2) => do
      return c2)
    (fun result => result)

-- InstCombineSimplifyRules.td:5674
def select_cond_true_cond : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let op1 ← MatchProg.root (.llvm .select) #[c2, op3.res[0]!, c2] #[t0]
      return (t0, c2))
    (fun (t0, c2) => do
      return c2)
    (fun result => result)

-- InstCombineSimplifyRules.td:5681
def nuw_add_ugt_self : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t1
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .icmp) #[op2.res[0]!, x3] #[t0] (fun p => p.predicate == .ugt)
      let () ← MatchProg.matchNative (t1, op4.properties) fun (m0, m1) => (((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (0))))
      return (t0, t1, x3, op4))
    (fun (t0, t1, x3, op4) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t1, op4.properties, t0) fun (m0, m1, m2) => some (integerConstant m2 (BitVec.ofNat 1 1).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- nsw_add_pos_sgt_self (InstCombineSimplifyRules.td:5687): not ported.
-- Source counterexample: C = 0 satisfies is_non_negative, but (X + 0) > X is false.

-- InstCombineSimplifyRules.td:5693
def nsw_add_neg_slt_self : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t1
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .icmp) #[op2.res[0]!, x3] #[t0] (fun p => p.predicate == .slt)
      let () ← MatchProg.matchNative (t1, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toInt < 0)))
      return (t0, t1, x3, op4))
    (fun (t0, t1, x3, op4) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t1, op4.properties, t0) fun (m0, m1, m2) => some (integerConstant m2 (BitVec.ofNat 1 1).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- select_i1_false_to_and (InstCombineSimplifyRules.td:5709): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- select_i1_true_to_or (InstCombineSimplifyRules.td:5723): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- select_i1_false_arm_to_andn (InstCombineSimplifyRules.td:5734): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- select_i1_true_arm_to_orn (InstCombineSimplifyRules.td:5742): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- gep_select_predecessor_index_factor_common_offset (InstCombineSimplifyRules.td:7643): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_scalar_constant_offset_to_ptradd_1 (InstCombineSimplifyRules.td:7754): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- gep_scalar_constant_offset_to_ptradd_2 (InstCombineSimplifyRules.td:7765): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- gep_scalar_constant_offset_to_ptradd_3 (InstCombineSimplifyRules.td:7776): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- gep_scalar_constant_offset_to_ptradd_4 (InstCombineSimplifyRules.td:7787): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- gep_scalar_constant_offset_to_ptradd_5 (InstCombineSimplifyRules.td:7799): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- gep_factor_first_variable_constant_tail_2 (InstCombineSimplifyRules.td:7814): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_factor_first_variable_constant_tail_3 (InstCombineSimplifyRules.td:7817): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_factor_first_variable_constant_tail_4 (InstCombineSimplifyRules.td:7820): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_factor_first_variable_constant_tail_5 (InstCombineSimplifyRules.td:7823): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_factor_first_variable_constant_tail_6 (InstCombineSimplifyRules.td:7826): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_factor_first_variable_constant_tail_7 (InstCombineSimplifyRules.td:7829): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_factor_first_variable_negative_array_tail_2 (InstCombineSimplifyRules.td:7834): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_linearize_first_variable_array_constant_tail_2 (InstCombineSimplifyRules.td:7838): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_linearize_first_variable_array_constant_tail_3 (InstCombineSimplifyRules.td:7841): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_linearize_first_variable_array_constant_tail_4 (InstCombineSimplifyRules.td:7844): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_linearize_first_variable_array_constant_tail_5 (InstCombineSimplifyRules.td:7847): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_linearize_first_variable_array_constant_tail_6 (InstCombineSimplifyRules.td:7850): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_linearize_first_variable_array_constant_tail_7 (InstCombineSimplifyRules.td:7853): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- InstCombineSimplifyRules.td:7857
/-- A single zero GEP index, either encoded as an attribute or an SSA operand. -/
def gep_zero_index : Array (CompiledPattern OpCode) :=
  #[false, true].map fun dynamic =>
    (Pattern.Builder
      (do
        let pointerType ← MatchProg.type (Attr := LLVM.PointerType)
        let pointer ← MatchProg.value pointerType
        let operands ← if dynamic then do
            let indexType ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
            let index ← MatchProg.operation (.llvm .mlir__constant) #[] #[indexType] (constantIs 0)
            pure #[pointer, index.res[0]!]
          else pure #[pointer]
        let _ ← MatchProg.root (.llvm .getelementptr) operands #[pointerType]
          (fun p => p.rawConstantIndices.values == #[if dynamic then -2147483648 else 0])
        return pointer)
      pure
      (fun pointer => pointer)).compile

-- gep_canonicalize_source_to_byte_array (InstCombineSimplifyRules.td:7866): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_constant_over_undef_gep_canonicalize_source (InstCombineSimplifyRules.td:7896): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_scalable_source_to_ptradd (InstCombineSimplifyRules.td:7907): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_scaled_mul_byte_array_to_ptradd (InstCombineSimplifyRules.td:7918): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_scaled_shl_byte_array_to_ptradd (InstCombineSimplifyRules.td:7927): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_constant_offset_to_ptradd (InstCombineSimplifyRules.td:7956): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- gep_constant_base_nonzero_index_to_ptradd_2 (InstCombineSimplifyRules.td:7986): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_constant_base_nonzero_index_to_ptradd_3 (InstCombineSimplifyRules.td:7999): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_constant_base_nonzero_index_to_ptradd_4 (InstCombineSimplifyRules.td:8012): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_constant_base_nonzero_index_to_ptradd_5 (InstCombineSimplifyRules.td:8025): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_const_i8_base_addlike_reassociate_inbounds_nuw (InstCombineSimplifyRules.td:8046): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_const_i8_base_addlike_reassociate_nuw (InstCombineSimplifyRules.td:8073): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_const_i8_base_addlike_reassociate_drop_flags (InstCombineSimplifyRules.td:8098): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_strip_trailing_zero_2 (InstCombineSimplifyRules.td:8125): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_strip_trailing_zero_3 (InstCombineSimplifyRules.td:8129): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_strip_trailing_zero_4 (InstCombineSimplifyRules.td:8133): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_strip_trailing_zero_5 (InstCombineSimplifyRules.td:8137): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_constant_prefix_3_leading_zero (InstCombineSimplifyRules.td:8145): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_constant_prefix_3_nonzero_first (InstCombineSimplifyRules.td:8157): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_constant_prefix_4_leading_zero (InstCombineSimplifyRules.td:8170): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_constant_prefix_4_nonzero_first (InstCombineSimplifyRules.td:8182): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_constant_prefix_5_leading_zero (InstCombineSimplifyRules.td:8196): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_constant_prefix_5_nonzero_first (InstCombineSimplifyRules.td:8209): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_second_nonzero_3_leading_zero (InstCombineSimplifyRules.td:8229): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_second_nonzero_4_leading_zero (InstCombineSimplifyRules.td:8242): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_strip_redundant_leading_zero_2_terminal (InstCombineSimplifyRules.td:8260): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- gep_strip_redundant_leading_zero_2 (InstCombineSimplifyRules.td:8276): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_fold_constant_terms_before_dynamic_suffix (InstCombineSimplifyRules.td:8287): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_split_sequential_nonzero_components (InstCombineSimplifyRules.td:8316): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_split_struct_nonzero_components (InstCombineSimplifyRules.td:8335): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_single_unit_offset_2 (InstCombineSimplifyRules.td:8352): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_single_unit_offset_3 (InstCombineSimplifyRules.td:8359): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_single_unit_offset_4 (InstCombineSimplifyRules.td:8366): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_single_unit_offset_5 (InstCombineSimplifyRules.td:8373): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_canonicalize_first_index_sext (InstCombineSimplifyRules.td:8384): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_canonicalize_first_index_zext (InstCombineSimplifyRules.td:8390): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_canonicalize_first_index_trunc (InstCombineSimplifyRules.td:8396): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_canonicalize_second_index_sext (InstCombineSimplifyRules.td:8402): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_canonicalize_second_index_zext (InstCombineSimplifyRules.td:8410): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_two_indices_canonicalize_second_index_trunc (InstCombineSimplifyRules.td:8418): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_three_indices_canonicalize_second_index_trunc (InstCombineSimplifyRules.td:8426): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_four_indices_canonicalize_second_index_trunc (InstCombineSimplifyRules.td:8432): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_five_indices_canonicalize_second_index_trunc (InstCombineSimplifyRules.td:8438): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_canonicalize_single_index_sext (InstCombineSimplifyRules.td:8448): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_canonicalize_single_index_zext (InstCombineSimplifyRules.td:8454): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_canonicalize_single_index_trunc (InstCombineSimplifyRules.td:8460): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_one_index_factor_phi_incoming_geps_varying_arg0 (InstCombineSimplifyRules.td:8480): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- gep_one_index_factor_phi_incoming_geps_varying_arg1 (InstCombineSimplifyRules.td:8501): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- gep_two_indices_factor_phi_incoming_geps_varying_arg0 (InstCombineSimplifyRules.td:8525): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- gep_two_indices_factor_phi_incoming_geps_varying_arg1 (InstCombineSimplifyRules.td:8548): not ported.
-- Requires LLVM PHI/incoming-edge rewrites; VeIR represents these with block arguments and Puddle
-- cannot rewrite CFG edges.

-- gep_split_one_use_sext_nsw_add_constant (InstCombineSimplifyRules.td:8575): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_nneg_zext_nsw_nuw_add_constant_preserve_flags (InstCombineSimplifyRules.td:8588): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_nneg_zext_nsw_add_constant_drop_flags (InstCombineSimplifyRules.td:8612): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_nneg_zext_disjoint_or_constant_preserve_flags (InstCombineSimplifyRules.td:8632): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_nneg_zext_disjoint_or_constant_drop_flags (InstCombineSimplifyRules.td:8652): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_nuw_addlike_index_preserve_flags (InstCombineSimplifyRules.td:8673): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_disjoint_or_index_dropping_flags (InstCombineSimplifyRules.td:8694): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_add_constant_index_dropping_flags (InstCombineSimplifyRules.td:8719): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_split_one_use_add_index_dropping_flags (InstCombineSimplifyRules.td:8735): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_gep_const_fold (InstCombineSimplifyRules.td:8749): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_chain_cancel_outer_subtrahend (InstCombineSimplifyRules.td:8768): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_chain_cancel_inner_subtrahend (InstCombineSimplifyRules.td:8777): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_chain_index_plus_complement (InstCombineSimplifyRules.td:8786): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_chain_negated_index_plus_add (InstCombineSimplifyRules.td:8795): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_sdiv_cancels_source_stride (InstCombineSimplifyRules.td:8810): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_udiv_cancels_source_stride (InstCombineSimplifyRules.td:8819): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_sdiv_factor_source_stride (InstCombineSimplifyRules.td:8832): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_udiv_factor_source_stride (InstCombineSimplifyRules.td:8851): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_lshr_cancels_source_stride (InstCombineSimplifyRules.td:8870): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_ashr_cancels_source_stride (InstCombineSimplifyRules.td:8880): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_lshr_factor_source_stride (InstCombineSimplifyRules.td:8890): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_exact_ashr_factor_source_stride (InstCombineSimplifyRules.td:8907): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_one_constant_index_through_constant_pointer_select (InstCombineSimplifyRules.td:8929): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_gep_inner_const_select_fold (InstCombineSimplifyRules.td:8947): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_gep_outer_const_select_fold (InstCombineSimplifyRules.td:8964): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_reassociate_constants_across_one_use_scaled_index (InstCombineSimplifyRules.td:8992): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- InstCombineSimplifyRules.td:9018
def add_select_consts_fold : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t7 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let cond3 ← MatchProg.value t7
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .select) #[cond3, op4.res[0]!, op5.res[0]!] #[t0]
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .add) (orient swaps 0 op2.res[0]! op6.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative t0 fun m0 => (((bitwidth m0) == (bitwidth m0)) && ((bitwidth m0) == (bitwidth m0)))
      return (t0, t7, cond3, op2, op4, op5, op6))
    (fun (t0, t7, cond3, op2, op4, op5, op6) => do
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op6.properties, op5.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 ((constantBits m0 m1) + (constantBits m0 m2)).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k8Props)
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op6.properties, op5.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 ((constantBits m0 m3) + (constantBits m0 m2)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let new7 ← CreateProg.operation (.llvm .select) #[cond3, k8.res[0]!, k9.res[0]!] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- select_one_index_geps_common_base (InstCombineSimplifyRules.td:9036): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- select_one_index_geps_common_index (InstCombineSimplifyRules.td:9055): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- select_one_index_gep_or_base (InstCombineSimplifyRules.td:9074): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- select_base_or_one_index_gep (InstCombineSimplifyRules.td:9087): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- icmp_#Comparison#_geps_same_constant_offset (InstCombineSimplifyRules.td:9103): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- icmp_eq_identical_single_index_geps (InstCombineSimplifyRules.td:9112): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- icmp_#Comparison#_same_base_single_index_gep_offsets (InstCombineSimplifyRules.td:9123): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- icmp_#Comparison#_inbounds_gep_null (InstCombineSimplifyRules.td:9137): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- icmp_#CMP#_inbounds_two_index_gep_null (InstCombineSimplifyRules.td:9150): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- icmp_#Comparison#_inbounds_gep_addrspacecast_null (InstCombineSimplifyRules.td:9164): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_srem_positive_pow2_to_mask (InstCombineSimplifyRules.td:9175): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- InstCombineSimplifyRules.td:9190
def uadd_overflow_zero : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__uadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def uadd_overflow_zero_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t2 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t2
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t2] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__uadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      return (t0, t1, t2, x3))
    (fun (t0, t1, t2, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def sadd_overflow_zero : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__sadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def sadd_overflow_zero_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t2 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t2
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t2] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__sadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      return (t0, t1, t2, x3))
    (fun (t0, t1, t2, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def usub_overflow_zero : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__usub__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def usub_overflow_zero_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t2 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t2
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t2] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__usub__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      return (t0, t1, t2, x3))
    (fun (t0, t1, t2, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def ssub_overflow_zero : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__ssub__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def ssub_overflow_zero_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t2 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t2
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t2] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .intr__ssub__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      return (t0, t1, t2, x3))
    (fun (t0, t1, t2, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9190
def smul_overflow_one : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let op2 ← MatchProg.operation (.llvm .intr__smul__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      return x3)
    (fun result => result)

-- smul_overflow_one_flag (InstCombineSimplifyRules.td:9190): not ported.
-- Source counterexample (i1): literal 1 is signed -1; multiplying X=-1 by it overflows, so the
-- flag is not always false.

-- InstCombineSimplifyRules.td:9206
def uadd_overflow_constant_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__uadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => (((constantBits m0 m1).toNat != 0))
      return (t0, t1, t5, x3, op4))
    (fun (t0, t1, t5, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (~~~(constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, k6.res[0]!] #[t0] (.inl { predicate := .ugt })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9212
def umul_overflow_constant_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umul__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => (((constantBits m0 m1).toNat != 0))
      return (t0, t1, t5, x3, op4))
    (fun (t0, t1, t5, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofInt (bitwidth m0) (-1)) / (constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, k6.res[0]!] #[t0] (.inl { predicate := .ugt })
      return new5.res[0]!)
    (fun result => result)

-- smul_overflow_constant_half_range_flag (InstCombineSimplifyRules.td:9225): not ported.
-- Requires the signed-multiply no-wrap interval calculator, including negative constants and
-- directed rounding.

-- smul_overflow_constant_interval_flag (InstCombineSimplifyRules.td:9235): not ported.
-- Requires the signed-multiply no-wrap interval calculator, including negative constants and
-- directed rounding.

-- InstCombineSimplifyRules.td:9247
def umul_overflow_i1_value : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__umul__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .and) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9251
def umul_overflow_i1_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t2 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t2
      let y4 ← MatchProg.value t2
      let op2 ← MatchProg.operation (.llvm .intr__umul__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      return (t0, t1, t2, x3, y4))
    (fun (t0, t1, t2, x3, y4) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9258
def ssub_overflow_constant_to_sadd : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t1
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__ssub__with__overflow) #[x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t1, op3.properties) fun (m0, m1) => (((constantBits m0 m1) != BitVec.intMin (bitwidth m0)) && ((constantBits m0 m1).toNat != 0))
      return (t0, t1, x2, op3))
    (fun (t0, t1, x2, op3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t1, op3.properties) fun (m0, m1) => some (integerConstant m0 (-(constantBits m0 m1)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t1] (.inr k5Props)
      let new4 ← CreateProg.operation (.llvm .intr__sadd__with__overflow) #[x2, k5.res[0]!] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- sadd_overflow_one_flag (InstCombineSimplifyRules.td:9267): not ported.
-- Source counterexample (i1): literal 1 is signed -1; X=0 does not overflow, but X==INT_MAX is
-- true.

-- InstCombineSimplifyRules.td:9272
def sadd_overflow_minus_one_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t4 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t4
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t4] (constantIs (-1))
      let op2 ← MatchProg.operation (.llvm .intr__sadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      return (t0, t1, t4, x3))
    (fun (t0, t1, t4, x3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t4 fun m0 => some (integerConstant m0 (BitVec.intMin (bitwidth m0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t4] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, k6.res[0]!] #[t0] (.inl { predicate := .eq })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9277
def sadd_overflow_positive_constant_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__sadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toInt > 0)) && ((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (1))))
      return (t0, t1, t5, x3, op4))
    (fun (t0, t1, t5, x3, op4) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.intMax (bitwidth m0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .sub) #[k7.res[0]!, op4.res[0]!] #[t5]
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, new6.res[0]!] #[t0] (.inl { predicate := .sgt })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9285
def sadd_overflow_negative_constant_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__sadd__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toInt < 0)) && ((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (-1))))
      return (t0, t1, t5, x3, op4))
    (fun (t0, t1, t5, x3, op4) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.intMin (bitwidth m0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .sub) #[k7.res[0]!, op4.res[0]!] #[t5]
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, new6.res[0]!] #[t0] (.inl { predicate := .slt })
      return new5.res[0]!)
    (fun result => result)

-- ssub_overflow_one_flag (InstCombineSimplifyRules.td:9295): not ported.
-- Source counterexample (i1): literal 1 is signed -1; X=0 overflows, but X==INT_MIN is false.

-- InstCombineSimplifyRules.td:9300
def ssub_overflow_minus_one_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t4 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t4
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t4] (constantIs (-1))
      let op2 ← MatchProg.operation (.llvm .intr__ssub__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      return (t0, t1, t4, x3))
    (fun (t0, t1, t4, x3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t4 fun m0 => some (integerConstant m0 (BitVec.intMax (bitwidth m0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t4] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, k6.res[0]!] #[t0] (.inl { predicate := .eq })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9305
def ssub_overflow_positive_constant_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__ssub__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toInt > 0)) && ((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (1))))
      return (t0, t1, t5, x3, op4))
    (fun (t0, t1, t5, x3, op4) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.intMin (bitwidth m0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .add) #[k7.res[0]!, op4.res[0]!] #[t5]
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, new6.res[0]!] #[t0] (.inl { predicate := .slt })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9313
def ssub_overflow_negative_constant_flag : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__ssub__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toInt < 0)) && ((constantBits m0 m1) != (BitVec.ofInt (bitwidth m0) (-1))))
      return (t0, t1, t5, x3, op4))
    (fun (t0, t1, t5, x3, op4) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.intMax (bitwidth m0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .add) #[k7.res[0]!, op4.res[0]!] #[t5]
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, new6.res[0]!] #[t0] (.inl { predicate := .sgt })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9328
def ctlz_bitreverse : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bitreverse) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctlz) #[op2.res[0]!] #[t0]
      return (t0, x3, op1))
    (fun (t0, x3, op1) => do
      let props5 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative op1.properties fun m0 => some { is_zero_poison := m0.is_zero_poison }
      let new4 ← CreateProg.operation (.llvm .intr__cttz) #[x3] #[t0] (.inr props5)
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9333
def cttz_bitreverse : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bitreverse) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0]
      return (t0, x3, op1))
    (fun (t0, x3, op1) => do
      let props5 : Handle OpCode (.prop (.llvm .intr__ctlz)) ←
        CreateProg.applyNative op1.properties fun m0 => some { is_zero_poison := m0.is_zero_poison }
      let new4 ← CreateProg.operation (.llvm .intr__ctlz) #[x3] #[t0] (.inr props5)
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9338
def ctpop_bitreverse : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bitreverse) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      return (t0, x3))
    (fun (t0, x3) => do
      let new4 ← CreateProg.operation (.llvm .intr__ctpop) #[x3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9343
def ctpop_bswap : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bswap) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      return (t0, x3))
    (fun (t0, x3) => do
      let new4 ← CreateProg.operation (.llvm .intr__ctpop) #[x3] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9348
def cttz_neg : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[op3.res[0]!, x4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0]
      return (t0, x4, op1))
    (fun (t0, x4, op1) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative op1.properties fun m0 => some { is_zero_poison := m0.is_zero_poison }
      let new5 ← CreateProg.operation (.llvm .intr__cttz) #[x4] #[t0] (.inr props6)
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9353
def cttz_abs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__abs) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0]
      return (t0, x3, op1))
    (fun (t0, x3, op1) => do
      let props5 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative op1.properties fun m0 => some { is_zero_poison := m0.is_zero_poison }
      let new4 ← CreateProg.operation (.llvm .intr__cttz) #[x3] #[t0] (.inr props5)
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9360
def ctpop_fshl_rotate : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let r4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__fshl) #[x3, x3, r4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      return (t0, x3, r4))
    (fun (t0, x3, r4) => do
      let new5 ← CreateProg.operation (.llvm .intr__ctpop) #[x3] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9365
def ctpop_fshr_rotate : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let r4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__fshr) #[x3, x3, r4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      return (t0, x3, r4))
    (fun (t0, x3, r4) => do
      let new5 ← CreateProg.operation (.llvm .intr__ctpop) #[x3] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9370
def umin_cttz_cttz : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__cttz) #[a3] #[t0]
      let b5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__cttz) #[b5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, a3, b5, op2, op4))
    (fun (t0, a3, b5, op2, op4) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative (op2.properties, op4.properties) fun (m0, m1) => some { is_zero_poison := (m0.is_zero_poison || m1.is_zero_poison) }
      let new8 ← CreateProg.operation (.llvm .or) #[a3, b5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__cttz) #[new8.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9376
def umin_ctlz_ctlz : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__ctlz) #[a3] #[t0]
      let b5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__ctlz) #[b5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, a3, b5, op2, op4))
    (fun (t0, a3, b5, op2, op4) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__ctlz)) ←
        CreateProg.applyNative (op2.properties, op4.properties) fun (m0, m1) => some { is_zero_poison := (m0.is_zero_poison || m1.is_zero_poison) }
      let new8 ← CreateProg.operation (.llvm .or) #[a3, b5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__ctlz) #[new8.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9383
def umin_cttz_constant_cap : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__cttz) #[x3] #[t0]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat < (bitwidth m0))))
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some { is_zero_poison := true }
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) 1) <<< (constantBits m0 m1).toNat).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k8Props)
      let new7 ← CreateProg.operation (.llvm .or) #[x3, k8.res[0]!] #[t0]
      let new5 ← CreateProg.operation (.llvm .intr__cttz) #[new7.res[0]!] #[t0] (.inr props6)
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9389
-- Same scalar pattern as `umin_cttz_constant_cap`; keep the source rule name.
def umin_constant_cttz_cap : Array (CompiledPattern OpCode) := umin_cttz_constant_cap

-- InstCombineSimplifyRules.td:9396
def umin_ctlz_constant_cap : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__ctlz) #[x3] #[t0]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat < (bitwidth m0))))
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__ctlz)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some { is_zero_poison := true }
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) 1) <<< ((bitwidth m0) - 1 - (constantBits m0 m1).toNat)).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k8Props)
      let new7 ← CreateProg.operation (.llvm .or) #[x3, k8.res[0]!] #[t0]
      let new5 ← CreateProg.operation (.llvm .intr__ctlz) #[new7.res[0]!] #[t0] (.inr props6)
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9402
-- Same scalar pattern as `umin_ctlz_constant_cap`; keep the source rule name.
def umin_constant_ctlz_cap : Array (CompiledPattern OpCode) := umin_ctlz_constant_cap

-- InstCombineSimplifyRules.td:9414
def i_cttz_with_poison_i1_zero_defined : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[x2] #[t0] (fun p => !p.is_zero_poison)
      return (t0, x2))
    (fun (t0, x2) => do
      let k4Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt 1 (-1)).toInt)
      let k4 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k4Props)
      let new3 ← CreateProg.operation (.llvm .xor) #[x2, k4.res[0]!] #[t0]
      return new3.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9414
def i_ctlz_with_poison_i1_zero_defined : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__ctlz) #[x2] #[t0] (fun p => !p.is_zero_poison)
      return (t0, x2))
    (fun (t0, x2) => do
      let k4Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt 1 (-1)).toInt)
      let k4 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k4Props)
      let new3 ← CreateProg.operation (.llvm .xor) #[x2, k4.res[0]!] #[t0]
      return new3.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9422
def i_cttz_with_poison_i1_zero_poison : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[x2] #[t0] (fun p => p.is_zero_poison)
      return (t0, x2))
    (fun (t0, x2) => do
      let k3Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k3 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k3Props)
      return k3.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9422
def i_ctlz_with_poison_i1_zero_poison : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x2 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__ctlz) #[x2] #[t0] (fun p => p.is_zero_poison)
      return (t0, x2))
    (fun (t0, x2) => do
      let k3Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k3 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k3Props)
      return k3.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9431
def umin_i_cttz_with_poison_i1_one : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__cttz) #[x3] #[t0] (fun p => p.is_zero_poison)
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      return (t0, x3))
    (fun (t0, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9431
def umin_i_ctlz_with_poison_i1_one : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__ctlz) #[x3] #[t0] (fun p => p.is_zero_poison)
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      return (t0, x3))
    (fun (t0, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9434
def umin_one_i_cttz_with_poison_i1 : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let op2 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__cttz) #[x4] #[t0] (fun p => p.is_zero_poison)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op3.res[0]!) #[t0]
      return (t0, x4))
    (fun (t0, x4) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9434
def umin_one_i_ctlz_with_poison_i1 : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let op2 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__ctlz) #[x4] #[t0] (fun p => p.is_zero_poison)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op3.res[0]!) #[t0]
      return (t0, x4))
    (fun (t0, x4) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat 1 0).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      return k5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9443
def brev_dist_i_bswap_and : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bswap) #[x3] #[t0]
      let y5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bswap) #[y5] #[t0]
      let op1 ← MatchProg.root (.llvm .and) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, x3, y5))
    (fun (t0, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .and) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__bswap) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9443
def brev_dist_i_bswap_or : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bswap) #[x3] #[t0]
      let y5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bswap) #[y5] #[t0]
      let op1 ← MatchProg.root (.llvm .or) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, x3, y5))
    (fun (t0, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .or) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__bswap) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9443
def brev_dist_i_bswap_xor : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bswap) #[x3] #[t0]
      let y5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bswap) #[y5] #[t0]
      let op1 ← MatchProg.root (.llvm .xor) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, x3, y5))
    (fun (t0, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .xor) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__bswap) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9443
def brev_dist_i_bitreverse_and : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bitreverse) #[x3] #[t0]
      let y5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bitreverse) #[y5] #[t0]
      let op1 ← MatchProg.root (.llvm .and) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, x3, y5))
    (fun (t0, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .and) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__bitreverse) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9443
def brev_dist_i_bitreverse_or : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bitreverse) #[x3] #[t0]
      let y5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bitreverse) #[y5] #[t0]
      let op1 ← MatchProg.root (.llvm .or) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, x3, y5))
    (fun (t0, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .or) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__bitreverse) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9443
def brev_dist_i_bitreverse_xor : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bitreverse) #[x3] #[t0]
      let y5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bitreverse) #[y5] #[t0]
      let op1 ← MatchProg.root (.llvm .xor) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, x3, y5))
    (fun (t0, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .xor) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__bitreverse) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9451
def or_bswap_const_distribute : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bswap) #[x3] #[t0]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .or) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 (byteSwap (constantBits m0 m1)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .or) #[x3, k7.res[0]!] #[t0]
      let new5 ← CreateProg.operation (.llvm .intr__bswap) #[new6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9455
def xor_bswap_const_distribute : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bswap) #[x3] #[t0]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .xor) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative () fun () => (true)
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 (byteSwap (constantBits m0 m1)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .xor) #[x3, k7.res[0]!] #[t0]
      let new5 ← CreateProg.operation (.llvm .intr__bswap) #[new6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9460
def or_bitreverse_const_distribute : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__bitreverse) #[x3] #[t0]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .or) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.reverse (constantBits m0 m1)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .or) #[x3, k7.res[0]!] #[t0]
      let new5 ← CreateProg.operation (.llvm .intr__bitreverse) #[new6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- bitreverse_and_mask_or_high_mask (InstCombineSimplifyRules.td:9473): not ported.
-- Source counterexample (i8): X=64, C=K=128 satisfies the leading-one guards, but gives 128
-- before and 130 after.

-- InstCombineSimplifyRules.td:9487
def abs_sext_to_zext_abs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t3 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t3
      let op2 ← MatchProg.operation (.llvm .sext) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t3, t0) fun (m0, m1) => (true && (decide ((bitwidth m0) < (bitwidth m1))))
      return (t0, t3, x3))
    (fun (t0, t3, x3) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative (t3, t0) fun (m0, m1) => some { is_int_min_poison := false }
      let new5 ← CreateProg.operation (.llvm .intr__abs) #[x3] #[t3] (.inr props6)
      let new4 ← CreateProg.operation (.llvm .zext) #[new5.res[0]!] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- abs_plain_known_nonnegative (InstCombineSimplifyRules.td:9494): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- abs_nsw_known_nonnegative (InstCombineSimplifyRules.td:9499): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- abs_plain_neg_one_minus_zext (InstCombineSimplifyRules.td:9508): not ported.
-- Source counterexample: zext i7 127 to i8 gives abs(-128,false)=-128, but the replacement add
-- nsw 127,1 is poison.

-- abs_plain_not_zext (InstCombineSimplifyRules.td:9518): not ported.
-- Source counterexample: zext i7 127 to i8 gives abs(~127,false)=-128, but the replacement add
-- nsw 127,1 is poison.

-- abs_plain_known_negative (InstCombineSimplifyRules.td:9527): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- abs_nsw_known_negative (InstCombineSimplifyRules.td:9532): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- abs_plain_known_nonpositive (InstCombineSimplifyRules.td:9541): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- abs_nsw_known_nonpositive (InstCombineSimplifyRules.td:9547): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- abs_plain_sub_with_known_reversed_order (InstCombineSimplifyRules.td:9556): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- abs_nsw_sub_with_known_reversed_order (InstCombineSimplifyRules.td:9563): not ported.
-- Requires LLVM signed/unsigned range and overflow proofs for unknown operands; no equivalent
-- LLVM value analysis is available in VeIR.

-- InstCombineSimplifyRules.td:9594
def fshl_drop_redundant_first_input_mask_for_rotate : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[op2.res[0]!, x3, op5.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat < (bitwidth m0)) && ((constantBits m0 m2).toNat &&& (2 ^ ((bitwidth m0) - (constantBits m0 m1).toNat) - 1)) == (2 ^ ((bitwidth m0) - (constantBits m0 m1).toNat) - 1)))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let new6 ← CreateProg.operation (.llvm .intr__fshl) #[x3, x3, op5.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- fshl_rotate_exact_high_mask_to_lshr (InstCombineSimplifyRules.td:9608): not ported.
-- Source permits Shift=0 and Mask=0, then creates lshr X,bitwidth (poison) from a defined zero
-- result.

-- InstCombineSimplifyRules.td:9621
def fshl_rotate_exact_low_mask_to_shl : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[op2.res[0]!, op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 2
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat < (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toNat)) && ((constantBits m0 m2) == ((BitVec.ofInt (bitwidth m0) (-1)) >>> (constantBits m0 m1).toNat)) && true)
      return (t0, x3, op2, op4, op5))
    (fun (t0, x3, op2, op4, op5) => do
      let new6 ← CreateProg.operation (.llvm .shl) #[x3, op5.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9633
def fshl_drop_noncontributing_masked_second_input : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op3 ← MatchProg.operation (.llvm .and) (orient swaps 0 x2 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[x2, op3.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op3.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat < (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toNat)) && (((constantBits m0 m2) &&& ((BitVec.ofInt (bitwidth m0) (-1)) <<< ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (constantBits m0 m1)).toNat)) == (BitVec.ofInt (bitwidth m0) (0))))
      return (t0, x2, op4, op5))
    (fun (t0, x2, op4, op5) => do
      let new6 ← CreateProg.operation (.llvm .shl) #[x2, op5.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9650
def fshl_rotate_or_exact_high_mask : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .or) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[op2.res[0]!, op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 2
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat < (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toNat)) && ((constantBits m0 m2) == ((BitVec.ofInt (bitwidth m0) (-1)) <<< ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (constantBits m0 m1)).toNat)) && true)
      return (t0, x3, op2, op4, op5))
    (fun (t0, x3, op2, op4, op5) => do
      let new6 ← CreateProg.operation (.llvm .intr__fshl) #[x3, op4.res[0]!, op5.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- fshl_first_mask_contributes_nothing (InstCombineSimplifyRules.td:9665): not ported.
-- Source permits Shift=0 and FirstMask=0, then creates lshr X,bitwidth (poison) from a defined
-- zero result.

-- fshl_zext_masked_narrow_amount (InstCombineSimplifyRules.td:9684): not ported.
-- Source lacks a power-of-two width premise: for i5 and an i4 amount, Mask=4 passes Mask+1=5 but
-- AND 4 is not reduction modulo 5.

-- fshr_zext_masked_narrow_amount (InstCombineSimplifyRules.td:9689): not ported.
-- Source lacks a power-of-two width premise: for i5 and an i4 amount, Mask=4 passes Mask+1=5 but
-- AND 4 is not reduction modulo 5.

-- InstCombineSimplifyRules.td:9696
def fshl_zero_lo_to_shl : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[x2, op3.res[0]!, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat < (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toNat)))
      return (t0, x2, op4))
    (fun (t0, x2, op4) => do
      let new5 ← CreateProg.operation (.llvm .shl) #[x2, op4.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9702
def fshr_zero_hi_to_lshr : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op2 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshr) #[op2.res[0]!, x3, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat < (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toNat)))
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let new5 ← CreateProg.operation (.llvm .lshr) #[x3, op4.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9712
def fshl_undef_lo_to_shl : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__undef) #[] #[t0]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[x2, op3.res[0]!, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => (true && (decide ((constantBits m0 m1).toNat < (bitwidth m0))))
      return (t0, x2, op3, op4))
    (fun (t0, x2, op3, op4) => do
      let new5 ← CreateProg.operation (.llvm .shl) #[x2, op4.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9719
def fshr_undef_hi_to_lshr : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op2 ← MatchProg.operation (.llvm .mlir__undef) #[] #[t0]
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshr) #[op2.res[0]!, x3, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => (true && (decide ((constantBits m0 m1).toNat < (bitwidth m0))))
      return (t0, op2, x3, op4))
    (fun (t0, op2, x3, op4) => do
      let new5 ← CreateProg.operation (.llvm .lshr) #[x3, op4.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9726
def fshl_zero_hi_to_lshr : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op2 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[op2.res[0]!, x3, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat < (bitwidth m0))) && ((constantBits m0 m1).toNat != 0))
      return (t0, x3, op4))
    (fun (t0, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .lshr) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9733
def fshl_undef_hi_to_lshr : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op2 ← MatchProg.operation (.llvm .mlir__undef) #[] #[t0]
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[op2.res[0]!, x3, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => (true && (decide ((constantBits m0 m1).toNat < (bitwidth m0))) && ((constantBits m0 m1).toNat != 0))
      return (t0, op2, x3, op4))
    (fun (t0, op2, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .lshr) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9741
def fshr_zero_lo_to_shl : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshr) #[x2, op3.res[0]!, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((decide ((constantBits m0 m1).toNat < (bitwidth m0))) && ((constantBits m0 m1).toNat != 0))
      return (t0, x2, op4))
    (fun (t0, x2, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .shl) #[x2, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9748
def fshr_undef_lo_to_shl : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__undef) #[] #[t0]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__fshr) #[x2, op3.res[0]!, op4.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => (true && (decide ((constantBits m0 m1).toNat < (bitwidth m0))) && ((constantBits m0 m1).toNat != 0))
      return (t0, x2, op3, op4))
    (fun (t0, x2, op3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .shl) #[x2, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:9835
def ssub_sat_to_sadd_sat : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__ssub__sat) #[x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op3.properties) fun (m0, m1) => ((!((constantBits m0 m1) == BitVec.intMin (bitwidth m0))))
      return (t0, x2, op3))
    (fun (t0, x2, op3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op3.properties) fun (m0, m1) => some (integerConstant m0 (-(constantBits m0 m1)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      let new4 ← CreateProg.operation (.llvm .intr__sadd__sat) #[x2, k5.res[0]!] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- infer_ptrmask_return_alignment (InstCombineSimplifyRules.td:9845): not ported.
-- VeIR has no llvm.ptrmask operation or pointer-mask property/analysis interface.

-- ptrmask_ptrmask (InstCombineSimplifyRules.td:9854): not ported.
-- VeIR has no llvm.ptrmask operation or pointer-mask property/analysis interface.

-- InstCombineSimplifyRules.td:10522
def smax_nsw_neg_to_neg_smin : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[op3.res[0]!, x4] #[t0] (fun p => p.nsw)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let y7 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .sub) #[op6.res[0]!, y7] #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x4, y7))
    (fun (t0, x4, y7) => do
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let new10 ← CreateProg.operation (.llvm .intr__smin) #[x4, y7] #[t0]
      let new8 ← CreateProg.operation (.llvm .sub) #[k9.res[0]!, new10.res[0]!] #[t0] (.inl { nsw := true, nuw := false })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10529
def smin_nsw_neg_to_neg_smax : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[op3.res[0]!, x4] #[t0] (fun p => p.nsw)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let y7 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .sub) #[op6.res[0]!, y7] #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x4, y7))
    (fun (t0, x4, y7) => do
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let new10 ← CreateProg.operation (.llvm .intr__smax) #[x4, y7] #[t0]
      let new8 ← CreateProg.operation (.llvm .sub) #[k9.res[0]!, new10.res[0]!] #[t0] (.inl { nsw := true, nuw := false })
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10537
def umin_one_to_zext_ne_zero : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t3 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t3
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t3] (constantIs (1))
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 x2 op3.res[0]!) #[t3]
      let () ← MatchProg.matchNative t3 fun m0 => (true && (decide (1 < (bitwidth m0))))
      return (t3, x2))
    (fun (t3, x2) => do
      let t2 ← CreateProg.type (IntegerType.signless 1)
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t3 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t3] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .icmp) #[x2, k6.res[0]!] #[t2] (.inl { predicate := .ne })
      let new4 ← CreateProg.operation (.llvm .zext) #[new5.res[0]!] #[t3]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10546
def umax_zext_zext : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t5
      let op2 ← MatchProg.operation (.llvm .zext) #[a3] #[t0]
      let b5 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .zext) #[b5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      let () ← MatchProg.matchNative (t5, t0) fun (m0, m1) => (((m0 == m0)) && (decide ((bitwidth m0) < (bitwidth m1))))
      return (t0, t5, a3, b5))
    (fun (t0, t5, a3, b5) => do
      let new7 ← CreateProg.operation (.llvm .intr__umax) #[a3, b5] #[t5]
      let new6 ← CreateProg.operation (.llvm .zext) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10546
def umin_zext_zext : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t5
      let op2 ← MatchProg.operation (.llvm .zext) #[a3] #[t0]
      let b5 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .zext) #[b5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      let () ← MatchProg.matchNative (t5, t0) fun (m0, m1) => (((m0 == m0)) && (decide ((bitwidth m0) < (bitwidth m1))))
      return (t0, t5, a3, b5))
    (fun (t0, t5, a3, b5) => do
      let new7 ← CreateProg.operation (.llvm .intr__umin) #[a3, b5] #[t5]
      let new6 ← CreateProg.operation (.llvm .zext) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10554
def smax_sext_sext : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t5
      let op2 ← MatchProg.operation (.llvm .sext) #[a3] #[t0]
      let b5 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .sext) #[b5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      let () ← MatchProg.matchNative (t5, t0) fun (m0, m1) => (((m0 == m0)) && (decide ((bitwidth m0) < (bitwidth m1))))
      return (t0, t5, a3, b5))
    (fun (t0, t5, a3, b5) => do
      let new7 ← CreateProg.operation (.llvm .intr__smax) #[a3, b5] #[t5]
      let new6 ← CreateProg.operation (.llvm .sext) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10554
def smin_sext_sext : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t5
      let op2 ← MatchProg.operation (.llvm .sext) #[a3] #[t0]
      let b5 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .sext) #[b5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 0 op2.res[0]! op4.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      let () ← MatchProg.matchNative (t5, t0) fun (m0, m1) => (((m0 == m0)) && (decide ((bitwidth m0) < (bitwidth m1))))
      return (t0, t5, a3, b5))
    (fun (t0, t5, a3, b5) => do
      let new7 ← CreateProg.operation (.llvm .intr__smin) #[a3, b5] #[t5]
      let new6 ← CreateProg.operation (.llvm .sext) #[new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10630
def extract_smul_ov_neg_one : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op2 ← MatchProg.operation (.llvm .intr__smul__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .sub) #[k6.res[0]!, x3] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10635
def extract_umul_ov_neg_one : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op2 ← MatchProg.operation (.llvm .intr__umul__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      return (t0, t1, x3))
    (fun (t0, t1, x3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .sub) #[k6.res[0]!, x3] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10644
def reassoc_const_i_umax : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toNat >= (constantBits m0 m2).toNat then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__umax) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10644
def reassoc_const_i_umin : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toNat <= (constantBits m0 m2).toNat then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__umin) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10644
def reassoc_const_i_smax : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toInt >= (constantBits m0 m2).toInt then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__smax) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10644
def reassoc_const_i_smin : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toInt <= (constantBits m0 m2).toInt then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__smin) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10651
def reassoc_var_const_i_umax : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y5 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 1 op2.res[0]! y5) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, y5, op4))
    (fun (t0, x3, y5, op4) => do
      let new7 ← CreateProg.operation (.llvm .intr__umax) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__umax) #[new7.res[0]!, op4.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10651
def reassoc_var_const_i_umin : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y5 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 1 op2.res[0]! y5) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, y5, op4))
    (fun (t0, x3, y5, op4) => do
      let new7 ← CreateProg.operation (.llvm .intr__umin) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__umin) #[new7.res[0]!, op4.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10651
def reassoc_var_const_i_smax : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y5 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 1 op2.res[0]! y5) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, y5, op4))
    (fun (t0, x3, y5, op4) => do
      let new7 ← CreateProg.operation (.llvm .intr__smax) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__smax) #[new7.res[0]!, op4.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10651
def reassoc_var_const_i_smin : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y5 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 1 op2.res[0]! y5) #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, y5, op4))
    (fun (t0, x3, y5, op4) => do
      let new7 ← CreateProg.operation (.llvm .intr__smin) #[x3, y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__smin) #[new7.res[0]!, op4.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10658
def extract_usubo_ov_to_ult : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let y4 ← MatchProg.value t5
      let op2 ← MatchProg.operation (.llvm .intr__usub__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      return (t0, t1, t5, x3, y4))
    (fun (t0, t1, t5, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .icmp) #[x3, y4] #[t0] (.inl { predicate := .ult })
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10664
def abs_srem_two : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (2))
      let op2 ← MatchProg.operation (.llvm .srem) #[x3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0]
      return (t0, x3))
    (fun (t0, x3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .and) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10670
def abs_select_neg_x : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c3 ← MatchProg.value t1
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x6 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .sub) #[op5.res[0]!, x6] #[t0]
      let op2 ← MatchProg.operation (.llvm .select) #[c3, op4.res[0]!, x6] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0] (fun p => !p.is_int_min_poison)
      return (t0, t1, c3, x6))
    (fun (t0, t1, c3, x6) => do
      let props8 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new7 ← CreateProg.operation (.llvm .intr__abs) #[x6] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10674
def abs_select_x_neg : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c3 ← MatchProg.value t1
      let x4 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op5 ← MatchProg.operation (.llvm .sub) #[op6.res[0]!, x4] #[t0]
      let op2 ← MatchProg.operation (.llvm .select) #[c3, x4, op5.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0] (fun p => !p.is_int_min_poison)
      return (t0, t1, c3, x4))
    (fun (t0, t1, c3, x4) => do
      let props8 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new7 ← CreateProg.operation (.llvm .intr__abs) #[x4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:10865
def smax_smin_clamp_canon : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt > (constantBits m0 m2).toInt)))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let new7 ← CreateProg.operation (.llvm .intr__smax) #[x3, op5.res[0]!] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__smin) #[new7.res[0]!, op4.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- signed_clamp_known_nonnegative_to_umin (InstCombineSimplifyRules.td:10875): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- InstCombineSimplifyRules.td:10885
def umax_umin_clamp_canon : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat > (constantBits m0 m2).toNat)))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let new7 ← CreateProg.operation (.llvm .intr__umax) #[x3, op5.res[0]!] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__umin) #[new7.res[0]!, op4.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11086
def ssub_ov_to_sadd_ov : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t1
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__ssub__with__overflow) #[x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t1, op3.properties) fun (m0, m1) => ((!((constantBits m0 m1) == BitVec.intMin (bitwidth m0))))
      return (t0, t1, x2, op3))
    (fun (t0, t1, x2, op3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t1, op3.properties) fun (m0, m1) => some (integerConstant m0 (-(constantBits m0 m1)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t1] (.inr k5Props)
      let new4 ← CreateProg.operation (.llvm .intr__sadd__with__overflow) #[x2, k5.res[0]!] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11093
def extract_ov1_smul_i1 : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__smul__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .and) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11146
def abs_mul_inner_abs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__abs) #[b5] #[t0] (fun p => p.is_int_min_poison)
      let op2 ← MatchProg.operation (.llvm .mul) (orient swaps 0 a3 op4.res[0]!) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0] (fun p => p.is_int_min_poison)
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, a3, b5))
    (fun (t0, a3, b5) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new8 ← CreateProg.operation (.llvm .mul) #[a3, b5] #[t0] (.inl { nsw := true, nuw := false })
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[new8.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11151
def abs_nsw_mul_inner_abs_plain : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__abs) #[b5] #[t0] (fun p => !p.is_int_min_poison)
      let op2 ← MatchProg.operation (.llvm .mul) (orient swaps 0 a3 op4.res[0]!) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0] (fun p => p.is_int_min_poison)
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, a3, b5))
    (fun (t0, a3, b5) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := true }
      let new8 ← CreateProg.operation (.llvm .mul) #[a3, b5] #[t0] (.inl { nsw := true, nuw := false })
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[new8.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11157
def abs_mul_inner_abs_plain : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__abs) #[b5] #[t0] (fun p => !p.is_int_min_poison)
      let op2 ← MatchProg.operation (.llvm .mul) (orient swaps 0 a3 op4.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0] (fun p => !p.is_int_min_poison)
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, a3, b5))
    (fun (t0, a3, b5) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new8 ← CreateProg.operation (.llvm .mul) #[a3, b5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[new8.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11165
def abs_nsw_wrapping_mul_inner_abs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__abs) #[b5] #[t0]
      let op2 ← MatchProg.operation (.llvm .mul) (orient swaps 0 a3 op4.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0] (fun p => p.is_int_min_poison)
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, a3, b5))
    (fun (t0, a3, b5) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := true }
      let new8 ← CreateProg.operation (.llvm .mul) #[a3, b5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[new8.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11170
def abs_plain_wrapping_mul_inner_abs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__abs) #[b5] #[t0]
      let op2 ← MatchProg.operation (.llvm .mul) (orient swaps 0 a3 op4.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0] (fun p => !p.is_int_min_poison)
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, a3, b5))
    (fun (t0, a3, b5) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new8 ← CreateProg.operation (.llvm .mul) #[a3, b5] #[t0]
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[new8.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11277
def i_smax_and_negpow2_factor : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y6 ← MatchProg.value t0
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 1 y6 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((isPowerOfTwo (-(constantBits m0 m1)).toNat))
      return (t0, x3, y6, op4))
    (fun (t0, x3, y6, op4) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, y6] #[t0]
      let new8 ← CreateProg.operation (.llvm .and) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11277
def i_smin_and_negpow2_factor : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y6 ← MatchProg.value t0
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 1 y6 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((isPowerOfTwo (-(constantBits m0 m1)).toNat))
      return (t0, x3, y6, op4))
    (fun (t0, x3, y6, op4) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, y6] #[t0]
      let new8 ← CreateProg.operation (.llvm .and) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11277
def i_umax_and_negpow2_factor : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y6 ← MatchProg.value t0
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 1 y6 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((isPowerOfTwo (-(constantBits m0 m1)).toNat))
      return (t0, x3, y6, op4))
    (fun (t0, x3, y6, op4) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, y6] #[t0]
      let new8 ← CreateProg.operation (.llvm .and) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11277
def i_umin_and_negpow2_factor : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let y6 ← MatchProg.value t0
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op5 ← MatchProg.operation (.llvm .and) (orient swaps 1 y6 op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      let () ← MatchProg.matchNative (op4.properties, op7.properties) fun (a, b) => constantIs (integerValue a) b
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((isPowerOfTwo (-(constantBits m0 m1)).toNat))
      return (t0, x3, y6, op4))
    (fun (t0, x3, y6, op4) => do
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, y6] #[t0]
      let new8 ← CreateProg.operation (.llvm .and) #[new9.res[0]!, op4.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11284
def cttz_sext_to_zext : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t3 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t3
      let op2 ← MatchProg.operation (.llvm .sext) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t3, t0) fun (m1, m2) => (true && (decide ((bitwidth m1) < (bitwidth m2))))
      return (t0, t3, x3, op1))
    (fun (t0, t3, x3, op1) => do
      let props5 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative (op1.properties, t3, t0) fun (m0, m1, m2) => some { is_zero_poison := m0.is_zero_poison }
      let new6 ← CreateProg.operation (.llvm .zext) #[x3] #[t0]
      let new4 ← CreateProg.operation (.llvm .intr__cttz) #[new6.res[0]!] #[t0] (.inr props5)
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11292
def cttz_zext_zero_poison_narrow : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t3 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t3
      let op2 ← MatchProg.operation (.llvm .zext) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0] (fun p => p.is_zero_poison)
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t3, t0) fun (m0, m1) => (true && (decide ((bitwidth m0) < (bitwidth m1))))
      return (t0, t3, x3))
    (fun (t0, t3, x3) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative (t3, t0) fun (m0, m1) => some { is_zero_poison := true }
      let new5 ← CreateProg.operation (.llvm .intr__cttz) #[x3] #[t3] (.inr props6)
      let new4 ← CreateProg.operation (.llvm .zext) #[new5.res[0]!] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11297
def ctpop_zext_narrow : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t3 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t3
      let op2 ← MatchProg.operation (.llvm .zext) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t3, t0) fun (m0, m1) => (true && (decide ((bitwidth m0) < (bitwidth m1))))
      return (t0, t3, x3))
    (fun (t0, t3, x3) => do
      let new5 ← CreateProg.operation (.llvm .intr__ctpop) #[x3] #[t3]
      let new4 ← CreateProg.operation (.llvm .zext) #[new5.res[0]!] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11307
def i_bswap_and_two_i_bswap_cancel : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bswap) #[x4] #[t0]
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .intr__bswap) #[y6] #[t0]
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 op3.res[0]! op5.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x4, y6))
    (fun (t0, x4, y6) => do
      let new7 ← CreateProg.operation (.llvm .and) #[x4, y6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11307
def i_bswap_or_two_i_bswap_cancel : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bswap) #[x4] #[t0]
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .intr__bswap) #[y6] #[t0]
      let op2 ← MatchProg.operation (.llvm .or) (orient swaps 0 op3.res[0]! op5.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x4, y6))
    (fun (t0, x4, y6) => do
      let new7 ← CreateProg.operation (.llvm .or) #[x4, y6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11307
def i_bswap_xor_two_i_bswap_cancel : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bswap) #[x4] #[t0]
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .intr__bswap) #[y6] #[t0]
      let op2 ← MatchProg.operation (.llvm .xor) (orient swaps 0 op3.res[0]! op5.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x4, y6))
    (fun (t0, x4, y6) => do
      let new7 ← CreateProg.operation (.llvm .xor) #[x4, y6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11307
def i_bitreverse_and_two_i_bitreverse_cancel : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bitreverse) #[x4] #[t0]
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .intr__bitreverse) #[y6] #[t0]
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 op3.res[0]! op5.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x4, y6))
    (fun (t0, x4, y6) => do
      let new7 ← CreateProg.operation (.llvm .and) #[x4, y6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11307
def i_bitreverse_or_two_i_bitreverse_cancel : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bitreverse) #[x4] #[t0]
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .intr__bitreverse) #[y6] #[t0]
      let op2 ← MatchProg.operation (.llvm .or) (orient swaps 0 op3.res[0]! op5.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x4, y6))
    (fun (t0, x4, y6) => do
      let new7 ← CreateProg.operation (.llvm .or) #[x4, y6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11307
def i_bitreverse_xor_two_i_bitreverse_cancel : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bitreverse) #[x4] #[t0]
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .intr__bitreverse) #[y6] #[t0]
      let op2 ← MatchProg.operation (.llvm .xor) (orient swaps 0 op3.res[0]! op5.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x4, y6))
    (fun (t0, x4, y6) => do
      let new7 ← CreateProg.operation (.llvm .xor) #[x4, y6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bswap_ordered_and_bswap_one_lhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bswap) #[x4] #[t0]
      let y5 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .and) #[op3.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      return (t0, x4, y5))
    (fun (t0, x4, y5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bswap) #[y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .and) #[x4, new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bswap_ordered_and_bswap_one_rhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bswap) #[x5] #[t0]
      let op2 ← MatchProg.operation (.llvm .and) #[y3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5))
    (fun (t0, y3, x5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bswap) #[y3] #[t0]
      let new6 ← CreateProg.operation (.llvm .and) #[new7.res[0]!, x5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bitrev_ordered_and_bitrev_one_lhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bitreverse) #[x4] #[t0]
      let y5 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .and) #[op3.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      return (t0, x4, y5))
    (fun (t0, x4, y5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bitreverse) #[y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .and) #[x4, new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bitrev_ordered_and_bitrev_one_rhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bitreverse) #[x5] #[t0]
      let op2 ← MatchProg.operation (.llvm .and) #[y3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5))
    (fun (t0, y3, x5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bitreverse) #[y3] #[t0]
      let new6 ← CreateProg.operation (.llvm .and) #[new7.res[0]!, x5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bswap_ordered_or_bswap_one_lhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bswap) #[x4] #[t0]
      let y5 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .or) #[op3.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      return (t0, x4, y5))
    (fun (t0, x4, y5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bswap) #[y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .or) #[x4, new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bswap_ordered_or_bswap_one_rhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bswap) #[x5] #[t0]
      let op2 ← MatchProg.operation (.llvm .or) #[y3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5))
    (fun (t0, y3, x5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bswap) #[y3] #[t0]
      let new6 ← CreateProg.operation (.llvm .or) #[new7.res[0]!, x5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bitrev_ordered_or_bitrev_one_lhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bitreverse) #[x4] #[t0]
      let y5 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .or) #[op3.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      return (t0, x4, y5))
    (fun (t0, x4, y5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bitreverse) #[y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .or) #[x4, new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bitrev_ordered_or_bitrev_one_rhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bitreverse) #[x5] #[t0]
      let op2 ← MatchProg.operation (.llvm .or) #[y3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5))
    (fun (t0, y3, x5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bitreverse) #[y3] #[t0]
      let new6 ← CreateProg.operation (.llvm .or) #[new7.res[0]!, x5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bswap_ordered_xor_bswap_one_lhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bswap) #[x4] #[t0]
      let y5 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .xor) #[op3.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      return (t0, x4, y5))
    (fun (t0, x4, y5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bswap) #[y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .xor) #[x4, new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bswap_ordered_xor_bswap_one_rhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bswap) #[x5] #[t0]
      let op2 ← MatchProg.operation (.llvm .xor) #[y3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bswap) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5))
    (fun (t0, y3, x5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bswap) #[y3] #[t0]
      let new6 ← CreateProg.operation (.llvm .xor) #[new7.res[0]!, x5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bitrev_ordered_xor_bitrev_one_lhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .intr__bitreverse) #[x4] #[t0]
      let y5 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .xor) #[op3.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      return (t0, x4, y5))
    (fun (t0, x4, y5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bitreverse) #[y5] #[t0]
      let new6 ← CreateProg.operation (.llvm .xor) #[x4, new7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11319
def bitrev_ordered_xor_bitrev_one_rhs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .intr__bitreverse) #[x5] #[t0]
      let op2 ← MatchProg.operation (.llvm .xor) #[y3, op4.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5))
    (fun (t0, y3, x5) => do
      let new7 ← CreateProg.operation (.llvm .intr__bitreverse) #[y3] #[t0]
      let new6 ← CreateProg.operation (.llvm .xor) #[new7.res[0]!, x5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11346
def clamp_smax_smin_two : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x3 op4.res[0]!) #[t5]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t5]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties, op5.properties) fun (m0, m1, m2) => (((constantBits m0 m1) == ((constantBits m0 m2) + (BitVec.ofInt (bitwidth m0) (1)))))
      return (t5, x3, op4, op5))
    (fun (t5, x3, op4, op5) => do
      let t4 ← CreateProg.type (IntegerType.signless 1)
      let new7 ← CreateProg.operation (.llvm .icmp) #[x3, op5.res[0]!] #[t4] (.inl { predicate := .sgt })
      let new6 ← CreateProg.operation (.llvm .select) #[new7.res[0]!, op4.res[0]!, op5.res[0]!] #[t5]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11351
def clamp_umax_umin_two : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op4.res[0]!) #[t5]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t5]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties, op5.properties) fun (m0, m1, m2) => (((constantBits m0 m1) == ((constantBits m0 m2) + (BitVec.ofInt (bitwidth m0) (1)))))
      return (t5, x3, op4, op5))
    (fun (t5, x3, op4, op5) => do
      let t4 ← CreateProg.type (IntegerType.signless 1)
      let new7 ← CreateProg.operation (.llvm .icmp) #[x3, op5.res[0]!] #[t4] (.inl { predicate := .ugt })
      let new6 ← CreateProg.operation (.llvm .select) #[new7.res[0]!, op4.res[0]!, op5.res[0]!] #[t5]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11360
def clamp_smin_smax_two : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op4.res[0]!) #[t5]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t5]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties, op5.properties) fun (m0, m1, m2) => (((constantBits m0 m1) != BitVec.intMax (bitwidth m0) && (constantBits m0 m2) == (constantBits m0 m1) + 1))
      return (t5, x3, op4, op5))
    (fun (t5, x3, op4, op5) => do
      let t4 ← CreateProg.type (IntegerType.signless 1)
      let new7 ← CreateProg.operation (.llvm .icmp) #[x3, op5.res[0]!] #[t4] (.inl { predicate := .slt })
      let new6 ← CreateProg.operation (.llvm .select) #[new7.res[0]!, op4.res[0]!, op5.res[0]!] #[t5]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11366
def clamp_umin_umax_two : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t5
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 0 x3 op4.res[0]!) #[t5]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t5]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t5, op4.properties, op5.properties) fun (m0, m1, m2) => (((constantBits m0 m1) != BitVec.allOnes (bitwidth m0) && (constantBits m0 m2) == (constantBits m0 m1) + 1))
      return (t5, x3, op4, op5))
    (fun (t5, x3, op4, op5) => do
      let t4 ← CreateProg.type (IntegerType.signless 1)
      let new7 ← CreateProg.operation (.llvm .icmp) #[x3, op5.res[0]!] #[t4] (.inl { predicate := .ult })
      let new6 ← CreateProg.operation (.llvm .select) #[new7.res[0]!, op4.res[0]!, op5.res[0]!] #[t5]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umax_nuw_add_dist_common_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common3 y6) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umax_nuw_add_dist_common_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common4) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umax_nuw_add_dist_crossed_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common3) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umax_nuw_add_dist_crossed_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common4 y6) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umin_nuw_add_dist_common_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common3 y6) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umin_nuw_add_dist_common_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common4) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umin_nuw_add_dist_crossed_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common3) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def umin_nuw_add_dist_crossed_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common4 y6) #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smax_nsw_add_dist_common_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common3 y6) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smax_nsw_add_dist_common_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common4) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smax_nsw_add_dist_crossed_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common3) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smax_nsw_add_dist_crossed_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common4 y6) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smin_nsw_add_dist_common_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common3 y6) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smin_nsw_add_dist_common_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common4) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smin_nsw_add_dist_crossed_left : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let common3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 common3 x4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 y6 common3) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, common3, x4, op2, y6, op5))
    (fun (t0, common3, x4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[common3, new9.res[0]!] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11382
def smin_nsw_add_dist_crossed_right : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let common4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 common4) #[t0] (fun p => p.nsw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .add) (orient swaps 1 common4 y6) #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 2 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, common4, op2, y6, op5))
    (fun (t0, x3, common4, op2, y6, op5) => do
      let props8 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (op2.properties, op5.properties) fun (m0, m1) => some { nsw := m0.nsw && m1.nsw, nuw := m0.nuw && m1.nuw }
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .add) #[new9.res[0]!, common4] #[t0] (.inr props8)
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11403
def umax_nuw_add_constant_dist : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op4.res[0]!) #[t0] (fun p => p.nuw)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat ≥ (constantBits m0 m2).toNat)))
      return (t0, x3, op2, op4, op5))
    (fun (t0, x3, op2, op4, op5) => do
      let props7 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some m3
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 ((constantBits m0 m1) - (constantBits m0 m2)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let new8 ← CreateProg.operation (.llvm .intr__umax) #[x3, k9.res[0]!] #[t0]
      let new6 ← CreateProg.operation (.llvm .add) #[new8.res[0]!, op4.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11407
def umin_nuw_add_constant_dist : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op4.res[0]!) #[t0] (fun p => p.nuw)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toNat ≥ (constantBits m0 m2).toNat)))
      return (t0, x3, op2, op4, op5))
    (fun (t0, x3, op2, op4, op5) => do
      let props7 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some m3
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 ((constantBits m0 m1) - (constantBits m0 m2)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[x3, k9.res[0]!] #[t0]
      let new6 ← CreateProg.operation (.llvm .add) #[new8.res[0]!, op4.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11411
def smax_nsw_add_constant_dist : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op4.res[0]!) #[t0] (fun p => p.nsw)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m1).toInt - (constantBits m0 m2).toInt) ∧ ((constantBits m0 m1).toInt - (constantBits m0 m2).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)))
      return (t0, x3, op2, op4, op5))
    (fun (t0, x3, op2, op4, op5) => do
      let props7 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some m3
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 ((constantBits m0 m1) - (constantBits m0 m2)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let new8 ← CreateProg.operation (.llvm .intr__smax) #[x3, k9.res[0]!] #[t0]
      let new6 ← CreateProg.operation (.llvm .add) #[new8.res[0]!, op4.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11415
def smin_nsw_add_constant_dist : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 x3 op4.res[0]!) #[t0] (fun p => p.nsw)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op4.properties) fun (m0, m1, m2) => ((decide ((BitVec.intMin (bitwidth m0)).toInt ≤ ((constantBits m0 m1).toInt - (constantBits m0 m2).toInt) ∧ ((constantBits m0 m1).toInt - (constantBits m0 m2).toInt) ≤ (BitVec.intMax (bitwidth m0)).toInt)))
      return (t0, x3, op2, op4, op5))
    (fun (t0, x3, op2, op4, op5) => do
      let props7 : Handle OpCode (.prop (.llvm .add)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some m3
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op5.properties, op4.properties, op2.properties) fun (m0, m1, m2, m3) => some (integerConstant m0 ((constantBits m0 m1) - (constantBits m0 m2)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let new8 ← CreateProg.operation (.llvm .intr__smin) #[x3, k9.res[0]!] #[t0]
      let new6 ← CreateProg.operation (.llvm .add) #[new8.res[0]!, op4.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11421
def umax_nuw_sub_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[a3, b4] #[t0] (fun p => p.nuw)
      let c6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .sub) #[c6, b4] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, a3, b4, c6))
    (fun (t0, a3, b4, c6) => do
      let new8 ← CreateProg.operation (.llvm .intr__umax) #[a3, c6] #[t0]
      let new7 ← CreateProg.operation (.llvm .sub) #[new8.res[0]!, b4] #[t0] (.inl { nsw := false, nuw := true })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11424
def umin_nuw_sub_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[a3, b4] #[t0] (fun p => p.nuw)
      let c6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .sub) #[c6, b4] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, a3, b4, c6))
    (fun (t0, a3, b4, c6) => do
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[a3, c6] #[t0]
      let new7 ← CreateProg.operation (.llvm .sub) #[new8.res[0]!, b4] #[t0] (.inl { nsw := false, nuw := true })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11427
def smax_nsw_sub_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[a3, b4] #[t0] (fun p => p.nsw)
      let c6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .sub) #[c6, b4] #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, a3, b4, c6))
    (fun (t0, a3, b4, c6) => do
      let new8 ← CreateProg.operation (.llvm .intr__smax) #[a3, c6] #[t0]
      let new7 ← CreateProg.operation (.llvm .sub) #[new8.res[0]!, b4] #[t0] (.inl { nsw := true, nuw := false })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11430
def smin_nsw_sub_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let a3 ← MatchProg.value t0
      let b4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[a3, b4] #[t0] (fun p => p.nsw)
      let c6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .sub) #[c6, b4] #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, a3, b4, c6))
    (fun (t0, a3, b4, c6) => do
      let new8 ← CreateProg.operation (.llvm .intr__smin) #[a3, c6] #[t0]
      let new7 ← CreateProg.operation (.llvm .sub) #[new8.res[0]!, b4] #[t0] (.inl { nsw := true, nuw := false })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11456
def cttz_and_neg_self : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x5 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .sub) #[op4.res[0]!, x5] #[t0]
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 0 op3.res[0]! x5) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0]
      return (t0, x5, op1))
    (fun (t0, x5, op1) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative op1.properties fun m0 => some { is_zero_poison := m0.is_zero_poison }
      let new6 ← CreateProg.operation (.llvm .intr__cttz) #[x5] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11463
def cttz_umin_one_shl_power_of_two : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let x5 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .shl) #[op4.res[0]!, x5] #[t0]
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 op3.res[0]! op6.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      let () ← MatchProg.matchNative (t0, op6.properties) fun (m0, m1) => ((isPowerOfTwo (constantBits m0 m1).toNat))
      return (t0, x5, op6))
    (fun (t0, x5, op6) => do
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op6.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (Nat.log2 (constantBits m0 m1).toNat)).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k8Props)
      let new7 ← CreateProg.operation (.llvm .intr__umin) #[x5, k8.res[0]!] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11476
def ctlz_umin_one_shl_power_of_two : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let x5 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .shl) #[op4.res[0]!, x5] #[t0]
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 op3.res[0]! op6.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctlz) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op3.op 1
      let () ← MatchProg.matchNative (t0, op6.properties) fun (m0, m1) => ((isPowerOfTwo (constantBits m0 m1).toNat))
      return (t0, x5, op6))
    (fun (t0, x5, op6) => do
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op6.properties) fun (m0, m1) => some (integerConstant m0 ((BitVec.ofNat (bitwidth m0) (bitwidth m0)) - (BitVec.ofInt (bitwidth m0) (1))).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k8Props)
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op6.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (Nat.log2 (constantBits m0 m1).toNat)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k10Props)
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x5, k10.res[0]!] #[t0]
      let new7 ← CreateProg.operation (.llvm .sub) #[k8.res[0]!, new9.res[0]!] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11491
def cttz_zero_poison_select_shifted_power_of_two_constants : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t8 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let cond3 ← MatchProg.value t8
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let trueshift6 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .shl) #[op5.res[0]!, trueshift6] #[t0]
      let op8 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let falseshift9 ← MatchProg.value t0
      let op7 ← MatchProg.operation (.llvm .shl) #[op8.res[0]!, falseshift9] #[t0]
      let op2 ← MatchProg.operation (.llvm .select) #[cond3, op4.res[0]!, op7.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0] (fun p => p.is_zero_poison)
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op5.properties, op8.properties) fun (m0, m1, m2) => ((isPowerOfTwo (constantBits m0 m1).toNat) && (isPowerOfTwo (constantBits m0 m2).toNat))
      return (t0, t8, cond3, trueshift6, falseshift9, op2, op5, op8))
    (fun (t0, t8, cond3, trueshift6, falseshift9, op2, op5, op8) => do
      let k12Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op5.properties, op8.properties) fun (m0, m1, m2) => some (integerConstant m0 (BitVec.ctz (constantBits m0 m1)).toInt)
      let k12 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k12Props)
      let new11 ← CreateProg.operation (.llvm .add) #[trueshift6, k12.res[0]!] #[t0]
      let k14Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op5.properties, op8.properties) fun (m0, m1, m2) => some (integerConstant m0 (BitVec.ctz (constantBits m0 m2)).toInt)
      let k14 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k14Props)
      let new13 ← CreateProg.operation (.llvm .add) #[falseshift9, k14.res[0]!] #[t0]
      let new10 ← CreateProg.operation (.llvm .select) #[cond3, new11.res[0]!, new13.res[0]!] #[t0]
      return new10.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11512
def extract_smul_ov_pow2 : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smul__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((isPowerOfTwo (constantBits m0 m1).toNat))
      return (t0, t1, x3, op4))
    (fun (t0, t1, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (Nat.log2 (constantBits m0 m1).toNat)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .shl) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11523
def extract_umul_ov_pow2 : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umul__with__overflow) #[x3, op4.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← MatchProg.matchNative (t0, op4.properties) fun (m0, m1) => ((isPowerOfTwo (constantBits m0 m1).toNat))
      return (t0, t1, x3, op4))
    (fun (t0, t1, x3, op4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (Nat.log2 (constantBits m0 m1).toNat)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .shl) #[x3, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11535
def extract_umul_self_overflow : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let t4 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t4
      let op2 ← MatchProg.operation (.llvm .intr__umul__with__overflow) #[x3, x3] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[1])
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative t4 fun m0 => (((bitwidth m0) % 2 == 0))
      return (t0, t1, t4, x3))
    (fun (t0, t1, t4, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t4 fun m0 => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (2 ^ ((bitwidth m0) / 2) - 1)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t4] (.inr k5Props)
      let new4 ← CreateProg.operation (.llvm .icmp) #[x3, k5.res[0]!] #[t0] (.inl { predicate := .ugt })
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11545
def ctlz_lshr_const_zero_poison : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .lshr) #[op3.res[0]!, x4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctlz) #[op2.res[0]!] #[t0] (fun p => p.is_zero_poison)
      return (t0, x4, op3))
    (fun (t0, x4, op3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op3.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.clz (constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .add) #[x4, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11549
def cttz_shl_const_zero_poison : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[op3.res[0]!, x4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0] (fun p => p.is_zero_poison)
      return (t0, x4, op3))
    (fun (t0, x4, op3) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op3.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ctz (constantBits m0 m1)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .add) #[x4, k6.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- lshr_nuw_shl_by_cttz_nuw_shl_pow2 (InstCombineSimplifyRules.td:11556): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- cttz_exact_lshr_const (InstCombineSimplifyRules.td:11568): not ported.
-- Source counterexample: C = 0, X = 1, zero-defined cttz gives width, not width - 1.

-- ctlz_nuw_shl_const (InstCombineSimplifyRules.td:11575): not ported.
-- Source counterexample: C = 0, X = 1, zero-defined ctlz gives width, not width - 1.

-- InstCombineSimplifyRules.td:11582
def cttz_lowmask_plus1 : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let x5 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .lshr) #[op4.res[0]!, x5] #[t0]
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 0 op3.res[0]! op6.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__cttz) #[op2.res[0]!] #[t0]
      return (t0, x5))
    (fun (t0, x5) => do
      let k8Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toInt)
      let k8 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k8Props)
      let new7 ← CreateProg.operation (.llvm .sub) #[k8.res[0]!, x5] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11589
def ctpop_or_neg_self : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op4 ← MatchProg.operation (.llvm .sub) #[op5.res[0]!, x3] #[t0]
      let op2 ← MatchProg.operation (.llvm .or) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3))
    (fun (t0, x3) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let props9 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative t0 fun m0 => some { is_zero_poison := false }
      let new8 ← CreateProg.operation (.llvm .intr__cttz) #[x3] #[t0] (.inr props9)
      let new6 ← CreateProg.operation (.llvm .sub) #[k7.res[0]!, new8.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11597
def ctpop_lowclear_mask : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op3 ← MatchProg.operation (.llvm .xor) (orient swaps 0 x4 op5.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op6 ← MatchProg.operation (.llvm .add) (orient swaps 1 x4 op7.res[0]!) #[t0]
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 2 op3.res[0]! op6.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      return (t0, x4))
    (fun (t0, x4) => do
      let props9 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative () fun () => some { is_zero_poison := false }
      let new8 ← CreateProg.operation (.llvm .intr__cttz) #[x4] #[t0] (.inr props9)
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11603
def ctpop_lowbit_minus_one : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op5 ← MatchProg.operation (.llvm .sub) #[op6.res[0]!, x4] #[t0]
      let op3 ← MatchProg.operation (.llvm .and) (orient swaps 0 x4 op5.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .add) (orient swaps 1 op3.res[0]! op7.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t0, op7.properties) fun (m0, m1) => (((constantBits m0 m1) == (BitVec.ofInt (bitwidth m0) (-1))))
      return (t0, x4, op7))
    (fun (t0, x4, op7) => do
      let props9 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative (t0, op7.properties) fun (m0, m1) => some { is_zero_poison := false }
      let new8 ← CreateProg.operation (.llvm .intr__cttz) #[x4] #[t0] (.inr props9)
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11609
def ctlz_lowclear_mask : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x4 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op3 ← MatchProg.operation (.llvm .xor) (orient swaps 0 x4 op5.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let op6 ← MatchProg.operation (.llvm .add) (orient swaps 1 x4 op7.res[0]!) #[t0]
      let op2 ← MatchProg.operation (.llvm .and) (orient swaps 2 op3.res[0]! op6.res[0]!) #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctlz) #[op2.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x4))
    (fun (t0, x4) => do
      let k9Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toInt)
      let k9 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k9Props)
      let props11 : Handle OpCode (.prop (.llvm .intr__cttz)) ←
        CreateProg.applyNative t0 fun m0 => some { is_zero_poison := false }
      let new10 ← CreateProg.operation (.llvm .intr__cttz) #[x4] #[t0] (.inr props11)
      let new8 ← CreateProg.operation (.llvm .sub) #[k9.res[0]!, new10.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11619
def fshl_i16_rotate8_to_bswap : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (8))
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[x2, x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative t0 fun m0 => (((bitwidth m0) == 16))
      return (t0, x2))
    (fun (t0, x2) => do
      let new4 ← CreateProg.operation (.llvm .intr__bswap) #[x2] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- recognize_bswap_bitreverse_fshl_root (InstCombineSimplifyRules.td:11630): not ported.
-- Requires LLVM byte/bit permutation recognition over an expression DAG; VeIR has no equivalent
-- recognizer.

-- recognize_bswap_bitreverse_fshr_root (InstCombineSimplifyRules.td:11636): not ported.
-- Requires LLVM byte/bit permutation recognition over an expression DAG; VeIR has no equivalent
-- recognizer.

-- InstCombineSimplifyRules.td:11647
def lshr_ctlz_log2bw_to_zext_eq_zero : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t4 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t4
      let op2 ← MatchProg.operation (.llvm .intr__ctlz) #[x3] #[t4]
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t4] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .lshr) #[op2.res[0]!, op4.res[0]!] #[t4]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t4, op4.properties) fun (m0, m1) => (((((BitVec.ofInt (bitwidth m0) (1)) <<< (constantBits m0 m1).toNat) == (BitVec.ofNat (bitwidth m0) (bitwidth m0)))) && (decide (1 < (bitwidth m0))))
      return (t4, x3, op4))
    (fun (t4, x3, op4) => do
      let t3 ← CreateProg.type (IntegerType.signless 1)
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t4, op4.properties) fun (m0, m1) => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t4] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .icmp) #[x3, k7.res[0]!] #[t3] (.inl { predicate := .eq })
      let new5 ← CreateProg.operation (.llvm .zext) #[new6.res[0]!] #[t4]
      return new5.res[0]!)
    (fun result => result)

-- fshr_const_to_fshl (InstCombineSimplifyRules.td:11655): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- InstCombineSimplifyRules.td:11667
def extract0_sole_use_umul_ov : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__umul__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← requireUses op2.op 1
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .mul) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11667
def extract0_sole_use_uadd_ov : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__uadd__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← requireUses op2.op 1
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .add) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11667
def extract0_sole_use_usub_ov : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__usub__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← requireUses op2.op 1
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .sub) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11667
def extract0_sole_use_sadd_ov : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__sadd__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← requireUses op2.op 1
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .add) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11667
def extract0_sole_use_ssub_ov : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__ssub__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← requireUses op2.op 1
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .sub) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11667
def extract0_sole_use_smul_ov : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := TypeAttr)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .intr__smul__with__overflow) #[x3, y4] #[t1]
      let op1 ← MatchProg.root (.llvm .extractvalue) #[op2.res[0]!] #[t0] (fun p => p.position.values == #[0])
      let () ← requireUses op2.op 1
      return (t0, t1, x3, y4))
    (fun (t0, t1, x3, y4) => do
      let new5 ← CreateProg.operation (.llvm .mul) #[x3, y4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- freeze_push_to_unique_poison_source (InstCombineSimplifyRules.td:11702): not ported.
-- Requires use-graph/dominance facts and coordinated sharing of an undef choice; a root-local
-- replacement cannot implement that policy.

-- freeze_share_choice_with_dominated_uses (InstCombineSimplifyRules.td:11711): not ported.
-- Requires use-graph/dominance facts and coordinated sharing of an undef choice; a root-local
-- replacement cannot implement that policy.

-- InstCombineSimplifyRules.td:11717
def ctpop_lshr_allones : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .lshr) #[op3.res[0]!, x4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      return (t0, x4))
    (fun (t0, x4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .sub) #[k6.res[0]!, x4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11723
def ctpop_shl_allones : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (-1))
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[op3.res[0]!, x4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__ctpop) #[op2.res[0]!] #[t0]
      return (t0, x4))
    (fun (t0, x4) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) (bitwidth m0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new5 ← CreateProg.operation (.llvm .sub) #[k6.res[0]!, x4] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11733
def abs_neg_to_abs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[op3.res[0]!, x4] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0]
      return (t0, x4))
    (fun (t0, x4) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new5 ← CreateProg.operation (.llvm .intr__abs) #[x4] #[t0] (.inr props6)
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11739
def smax_opposite_nsw_subtractions_to_nsw_abs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[x3, y4] #[t0] (fun p => p.nsw)
      let op5 ← MatchProg.operation (.llvm .sub) #[y4, x3] #[t0] (fun p => p.nsw)
      let op1 ← MatchProg.root (.llvm .intr__smax) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, y4, op2))
    (fun (t0, x3, y4, op2) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := true }
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[op2.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11746
def smax_opposite_consumed_subtractions_to_abs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[x3, y4] #[t0]
      let op5 ← MatchProg.operation (.llvm .sub) #[y4, x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smax) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, y4, op2))
    (fun (t0, x3, y4, op2) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[op2.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11755
def smax_opposite_subtractions_reuse_rhs_as_abs : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let y4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[x3, y4] #[t0]
      let op5 ← MatchProg.operation (.llvm .sub) #[y4, x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smax) #[op2.res[0]!, op5.res[0]!] #[t0]
      let () ← requireUses op2.op 1
      return (t0, x3, y4, op5))
    (fun (t0, x3, y4, op5) => do
      let props7 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new6 ← CreateProg.operation (.llvm .intr__abs) #[op5.res[0]!] #[t0] (.inr props7)
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11761
def smax_x_neg_x_to_abs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op3 ← MatchProg.operation (.llvm .sub) #[op4.res[0]!, x2] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 0 x2 op3.res[0]!) #[t0]
      return (t0, x2))
    (fun (t0, x2) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new5 ← CreateProg.operation (.llvm .intr__abs) #[x2] #[t0] (.inr props6)
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11766
def smin_x_neg_x_to_nabs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op3 ← MatchProg.operation (.llvm .sub) #[op4.res[0]!, x2] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 0 x2 op3.res[0]!) #[t0]
      return (t0, x2))
    (fun (t0, x2) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let props8 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative t0 fun m0 => some { is_int_min_poison := false }
      let new7 ← CreateProg.operation (.llvm .intr__abs) #[x2] #[t0] (.inr props8)
      let new5 ← CreateProg.operation (.llvm .sub) #[k6.res[0]!, new7.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11771
def umin_x_neg_x_to_abs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op3 ← MatchProg.operation (.llvm .sub) #[op4.res[0]!, x2] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 x2 op3.res[0]!) #[t0]
      return (t0, x2))
    (fun (t0, x2) => do
      let props6 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative () fun () => some { is_int_min_poison := false }
      let new5 ← CreateProg.operation (.llvm .intr__abs) #[x2] #[t0] (.inr props6)
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11776
def umax_x_neg_x_to_nabs : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op3 ← MatchProg.operation (.llvm .sub) #[op4.res[0]!, x2] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 0 x2 op3.res[0]!) #[t0]
      return (t0, x2))
    (fun (t0, x2) => do
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let props8 : Handle OpCode (.prop (.llvm .intr__abs)) ←
        CreateProg.applyNative t0 fun m0 => some { is_int_min_poison := false }
      let new7 ← CreateProg.operation (.llvm .intr__abs) #[x2] #[t0] (.inr props8)
      let new5 ← CreateProg.operation (.llvm .sub) #[k6.res[0]!, new7.res[0]!] #[t0]
      return new5.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11790
def umin_nuw_shl_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let c4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[x3, c4] #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .shl) #[y6, c4] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, c4, y6))
    (fun (t0, x3, c4, y6) => do
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .shl) #[new8.res[0]!, c4] #[t0] (.inl { nsw := false, nuw := true })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11794
def umax_nuw_shl_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let c4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[x3, c4] #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .shl) #[y6, c4] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op5.op 1
      return (t0, x3, c4, y6))
    (fun (t0, x3, c4, y6) => do
      let new8 ← CreateProg.operation (.llvm .intr__umax) #[x3, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .shl) #[new8.res[0]!, c4] #[t0] (.inl { nsw := false, nuw := true })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11801
def fshl_rotate_neg_to_fshr : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let y5 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .sub) #[op4.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__fshl) #[x2, x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative t0 fun m0 => ((isPowerOfTwo (bitwidth m0)))
      return (t0, x2, y5))
    (fun (t0, x2, y5) => do
      let new6 ← CreateProg.operation (.llvm .intr__fshr) #[x2, x2, y5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11807
def fshr_rotate_neg_to_fshl : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x2 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let y5 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .sub) #[op4.res[0]!, y5] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__fshr) #[x2, x2, op3.res[0]!] #[t0]
      let () ← MatchProg.matchNative t0 fun m0 => ((isPowerOfTwo (bitwidth m0)))
      return (t0, x2, y5))
    (fun (t0, x2, y5) => do
      let new6 ← CreateProg.operation (.llvm .intr__fshl) #[x2, x2, y5] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11815
def abs_zext_elim : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t2 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t2
      let op2 ← MatchProg.operation (.llvm .zext) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__abs) #[op2.res[0]!] #[t0]
      return (t0, t2, x3, op2))
    (fun (t0, t2, x3, op2) => do
      return op2.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:11975
-- Same scalar pattern as `select_eq_zero_self`; keep the source rule name.
def select_eq_zero_identity : Array (CompiledPattern OpCode) := select_eq_zero_self

-- InstCombineSimplifyRules.td:11979
-- Same scalar pattern as `select_ne_zero_self`; keep the source rule name.
def select_ne_zero_identity : Array (CompiledPattern OpCode) := select_ne_zero_self

-- InstCombineSimplifyRules.td:12011
def select_eq_const_identity : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.predicate == .eq)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, x3] #[t0]
      let () ← MatchProg.matchNative (op4.properties, op5.properties) fun (a, b) => constantIs (integerValue a) b
      return (t0, t1, x3, op4))
    (fun (t0, t1, x3, op4) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:12016
def select_ne_const_identity : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.predicate == .ne)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, x3, op5.res[0]!] #[t0]
      let () ← MatchProg.matchNative (op4.properties, op5.properties) fun (a, b) => constantIs (integerValue a) b
      return (t0, t1, x3, op4))
    (fun (t0, t1, x3, op4) => do
      return x3)
    (fun result => result)

-- InstCombineSimplifyRules.td:12021
def select_eq_zero_or : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.predicate == .eq)
      let y5 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .or) (orient swaps 1 x3 y5) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, y5, op6.res[0]!] #[t0]
      return (t0, t1, x3, y5))
    (fun (t0, t1, x3, y5) => do
      let new7 ← CreateProg.operation (.llvm .or) #[x3, y5] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12026
def select_ne_zero_or : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (0))
      let op2 ← MatchProg.operation (.llvm .icmp) (orient swaps 0 x3 op4.res[0]!) #[t1] (fun p => p.predicate == .ne)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .or) (orient swaps 1 x3 y6) #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[op2.res[0]!, op5.res[0]!, y6] #[t0]
      return (t0, t1, x3, y6))
    (fun (t0, t1, x3, y6) => do
      let new7 ← CreateProg.operation (.llvm .or) #[x3, y6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12057
def reassociate_three_smax_constants : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op4 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x5 op6.res[0]!) #[t0]
      let op2 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 1 y3 op4.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smax) (orient swaps 2 op2.res[0]! op7.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5, op6, op7))
    (fun (t0, y3, x5, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smax) #[x5, y3] #[t0]
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op6.properties, op7.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toInt >= (constantBits m0 m2).toInt then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k10Props)
      let new8 ← CreateProg.operation (.llvm .intr__smax) #[new9.res[0]!, k10.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12060
def reassociate_three_smin_constants : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op4 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 0 x5 op6.res[0]!) #[t0]
      let op2 ← MatchProg.operation (.llvm .intr__smin) (orient swaps 1 y3 op4.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 2 op2.res[0]! op7.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5, op6, op7))
    (fun (t0, y3, x5, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__smin) #[x5, y3] #[t0]
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op6.properties, op7.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toInt <= (constantBits m0 m2).toInt then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k10Props)
      let new8 ← CreateProg.operation (.llvm .intr__smin) #[new9.res[0]!, k10.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12063
def reassociate_three_umax_constants : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op4 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 0 x5 op6.res[0]!) #[t0]
      let op2 ← MatchProg.operation (.llvm .intr__umax) (orient swaps 1 y3 op4.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 2 op2.res[0]! op7.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5, op6, op7))
    (fun (t0, y3, x5, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umax) #[x5, y3] #[t0]
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op6.properties, op7.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toNat >= (constantBits m0 m2).toNat then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k10Props)
      let new8 ← CreateProg.operation (.llvm .intr__umax) #[new9.res[0]!, k10.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12066
def reassociate_three_umin_constants : Array (CompiledPattern OpCode) :=
  compileVariants 3 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let y3 ← MatchProg.value t0
      let x5 ← MatchProg.value t0
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op4 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x5 op6.res[0]!) #[t0]
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 1 y3 op4.res[0]!) #[t0]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 2 op2.res[0]! op7.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← requireUses op4.op 1
      return (t0, y3, x5, op6, op7))
    (fun (t0, y3, x5, op6, op7) => do
      let new9 ← CreateProg.operation (.llvm .intr__umin) #[x5, y3] #[t0]
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op6.properties, op7.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toNat <= (constantBits m0 m2).toNat then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k10Props)
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[new9.res[0]!, k10.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12070
-- Same scalar pattern as `reassoc_const_i_smax`; keep the source rule name.
def smax_smax_const_fold : Array (CompiledPattern OpCode) := reassoc_const_i_smax

-- InstCombineSimplifyRules.td:12077
-- Same scalar pattern as `reassoc_const_i_smin`; keep the source rule name.
def smin_smin_const_fold : Array (CompiledPattern OpCode) := reassoc_const_i_smin

-- InstCombineSimplifyRules.td:12084
-- Same scalar pattern as `reassoc_const_i_umax`; keep the source rule name.
def umax_umax_const_fold : Array (CompiledPattern OpCode) := reassoc_const_i_umax

-- InstCombineSimplifyRules.td:12091
-- Same scalar pattern as `reassoc_const_i_umin`; keep the source rule name.
def umin_umin_const_fold : Array (CompiledPattern OpCode) := reassoc_const_i_umin

-- InstCombineSimplifyRules.td:12103
def umax_smax_nonnegative_constants_fold : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__smax) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt >= 0)) && (decide ((constantBits m0 m2).toInt >= 0)))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toInt >= (constantBits m0 m2).toInt then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__smax) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12113
def smin_umin_nonnegative_constants_fold : Array (CompiledPattern OpCode) :=
  compileVariants 2 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let x3 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .intr__umin) (orient swaps 0 x3 op4.res[0]!) #[t0]
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__smin) (orient swaps 1 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireUses op2.op 1
      let () ← MatchProg.matchNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => ((decide ((constantBits m0 m1).toInt >= 0)) && (decide ((constantBits m0 m2).toInt >= 0)))
      return (t0, x3, op4, op5))
    (fun (t0, x3, op4, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op4.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (if (constantBits m0 m1).toNat <= (constantBits m0 m2).toNat then (constantBits m0 m1) else (constantBits m0 m2)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__umin) #[x3, k7.res[0]!] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- umax_xor_pow2_to_or (InstCombineSimplifyRules.td:12133): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- umin_xor_pow2_to_andn (InstCombineSimplifyRules.td:12138): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- InstCombineSimplifyRules.td:12150
def bitreverse_zext_i1_to_select : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t3 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x3 ← MatchProg.value t3
      let op2 ← MatchProg.operation (.llvm .zext) #[x3] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__bitreverse) #[op2.res[0]!] #[t0]
      return (t0, t3, x3))
    (fun (t0, t3, x3) => do
      let k5Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.intMin (bitwidth m0)).toInt)
      let k5 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k5Props)
      let k6Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k6 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k6Props)
      let new4 ← CreateProg.operation (.llvm .select) #[x3, k5.res[0]!, k6.res[0]!] #[t0]
      return new4.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12158
def bitreverse_zext_i1_not_sign_extract : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x6 ← MatchProg.value t5
      let op5 ← MatchProg.operation (.llvm .zext) #[x6] #[t1]
      let op4 ← MatchProg.operation (.llvm .intr__bitreverse) #[op5.res[0]!] #[t1]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] (constantIs (-1))
      let op3 ← MatchProg.operation (.llvm .xor) (orient swaps 0 op4.res[0]! op7.res[0]!) #[t1]
      let op8 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t1] isIntegerConstant
      let op2 ← MatchProg.operation (.llvm .lshr) #[op3.res[0]!, op8.res[0]!] #[t1]
      let op1 ← MatchProg.root (.llvm .zext) #[op2.res[0]!] #[t0]
      let () ← MatchProg.matchNative (t1, op8.properties, t0) fun (m0, m1, m3) => ((((constantBits m0 m1).toNat == (bitwidth m0) - 1)) && (decide (1 < (bitwidth m3))))
      return (t0, t1, t5, x6, op8))
    (fun (t0, t1, t5, x6, op8) => do
      let k11Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t1, op8.properties, t5, t0) fun (m0, m1, m2, m3) => some (integerConstant m2 (BitVec.ofInt 1 (-1)).toInt)
      let k11 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k11Props)
      let new10 ← CreateProg.operation (.llvm .xor) #[x6, k11.res[0]!] #[t5]
      let new9 ← CreateProg.operation (.llvm .zext) #[new10.res[0]!] #[t0]
      return new9.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12165
def bitreverse_i1_select_not_sign_extract : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t1 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let t2 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let x4 ← MatchProg.value t5
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t2] (constantExtreme true)
      let op6 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t2] (constantIs (0))
      let op3 ← MatchProg.operation (.llvm .select) #[x4, op5.res[0]!, op6.res[0]!] #[t2]
      let op7 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t2] (constantIs (-1))
      let op2 ← MatchProg.operation (.llvm .icmp) #[op3.res[0]!, op7.res[0]!] #[t1] (fun p => p.predicate == .sgt)
      let op1 ← MatchProg.root (.llvm .zext) #[op2.res[0]!] #[t0]
      let () ← MatchProg.matchNative t0 fun m1 => (true && (decide (1 < (bitwidth m1))))
      return (t0, t1, t2, t5, x4))
    (fun (t0, t1, t2, t5, x4) => do
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t5, t0) fun (m0, m1) => some (integerConstant m0 (BitVec.ofInt 1 (-1)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t5] (.inr k10Props)
      let new9 ← CreateProg.operation (.llvm .xor) #[x4, k10.res[0]!] #[t5]
      let new8 ← CreateProg.operation (.llvm .zext) #[new9.res[0]!] #[t0]
      return new8.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12170
def usub_sat_nuwsub_const : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let a4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[op3.res[0]!, a4] #[t0] (fun p => p.nuw)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__usub__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      return (t0, a4, op3, op5))
    (fun (t0, a4, op3, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op3.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) ((constantBits m0 m1).toNat - (constantBits m0 m2).toNat)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__usub__sat) #[k7.res[0]!, a4] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12177
def select_nested_same_cond_false : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr) (fun t => t.isa IntegerType || t.isa LLVM.PointerType)
      let t7 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c2 ← MatchProg.value t7
      let x3 ← MatchProg.value t0
      let y5 ← MatchProg.value t0
      let z6 ← MatchProg.value t0
      let op4 ← MatchProg.operation (.llvm .select) #[c2, y5, z6] #[t0]
      let op1 ← MatchProg.root (.llvm .select) #[c2, x3, op4.res[0]!] #[t0]
      return (t0, t7, c2, x3, y5, z6))
    (fun (t0, t7, c2, x3, y5, z6) => do
      let new7 ← CreateProg.operation (.llvm .select) #[c2, x3, z6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12179
def select_nested_same_cond_true : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := TypeAttr) (fun t => t.isa IntegerType || t.isa LLVM.PointerType)
      let t7 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let c2 ← MatchProg.value t7
      let x4 ← MatchProg.value t0
      let y5 ← MatchProg.value t0
      let op3 ← MatchProg.operation (.llvm .select) #[c2, x4, y5] #[t0]
      let z6 ← MatchProg.value t0
      let op1 ← MatchProg.root (.llvm .select) #[c2, op3.res[0]!, z6] #[t0]
      return (t0, t7, c2, x4, y5, z6))
    (fun (t0, t7, c2, x4, y5, z6) => do
      let new7 ← CreateProg.operation (.llvm .select) #[c2, x4, z6] #[t0]
      return new7.res[0]!)
    (fun result => result)

-- gep_infer_inbounds_and_nuw_from_dereferenceable_object (InstCombineSimplifyRules.td:12227): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_infer_nuw_from_nusw_nonnegative (InstCombineSimplifyRules.td:12236): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- gep_infer_inbounds_from_dereferenceable_object (InstCombineSimplifyRules.td:12244): not ported.
-- Requires TIC's typed GEP index/offset or no-wrap descriptor program. VeIR's RV64 lowering
-- helpers do not supply these target-independent source-type and flag contracts.

-- InstCombineSimplifyRules.td:12564
def usub_sat_nuwsub_constant_lanes : Array (CompiledPattern OpCode) :=
  compileVariants 0 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let op3 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .sub) #[op3.res[0]!, x4] #[t0] (fun p => p.nuw)
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] isIntegerConstant
      let op1 ← MatchProg.root (.llvm .intr__usub__sat) #[op2.res[0]!, op5.res[0]!] #[t0]
      return (t0, x4, op3, op5))
    (fun (t0, x4, op3, op5) => do
      let k7Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative (t0, op3.properties, op5.properties) fun (m0, m1, m2) => some (integerConstant m0 (BitVec.ofNat (bitwidth m0) ((constantBits m0 m1).toNat - (constantBits m0 m2).toNat)).toInt)
      let k7 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k7Props)
      let new6 ← CreateProg.operation (.llvm .intr__usub__sat) #[k7.res[0]!, x4] #[t0]
      return new6.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12574
def usub_sat_select_one_zext_not_condition : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let t5 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth == 1)
      let cond3 ← MatchProg.value t5
      let x4 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t0] (constantIs (1))
      let op2 ← MatchProg.operation (.llvm .select) #[cond3, x4, op5.res[0]!] #[t0]
      let op8 ← MatchProg.operation (.llvm .mlir__constant) #[] #[t5] (constantIs (-1))
      let op7 ← MatchProg.operation (.llvm .xor) (orient swaps 0 cond3 op8.res[0]!) #[t5]
      let op6 ← MatchProg.operation (.llvm .zext) #[op7.res[0]!] #[t0]
      let op1 ← MatchProg.root (.llvm .intr__usub__sat) #[op2.res[0]!, op6.res[0]!] #[t0]
      return (t0, t5, cond3, x4))
    (fun (t0, t5, cond3, x4) => do
      let k10Props : Handle OpCode (.prop (.llvm .mlir__constant)) ←
        CreateProg.applyNative t0 fun m0 => some (integerConstant m0 (BitVec.ofInt (bitwidth m0) (0)).toInt)
      let k10 ← CreateProg.operation (.llvm .mlir__constant) #[] #[t0] (.inr k10Props)
      let new9 ← CreateProg.operation (.llvm .select) #[cond3, x4, k10.res[0]!] #[t0]
      return new9.res[0]!)
    (fun result => result)

-- smax_xor_nonnegative_pow2_to_or (InstCombineSimplifyRules.td:12582): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- smin_xor_nonnegative_pow2_to_andn (InstCombineSimplifyRules.td:12589): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- smax_xor_proven_signed_min_to_andn (InstCombineSimplifyRules.td:12598): not ported.
-- Requires path-sensitive signed-minimum inference from dominating conditions; the existing
-- dominance analysis does not prove this value fact.

-- smax_xor_negative_pow2_to_andn (InstCombineSimplifyRules.td:12605): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- smin_xor_negative_pow2_to_or (InstCombineSimplifyRules.td:12612): not ported.
-- Requires LLVM value-tracking facts (known bits/ranges or guaranteed non-poison values); the
-- existing VeIR constant/modular analyses do not supply this contract.

-- InstCombineSimplifyRules.td:12632
def umin_nuw_shl_common_lhs_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let base3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[base3, x4] #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .shl) #[base3, y6] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireEitherOperandOneUse op1.op
      let () ← MatchProg.matchNative (op2.properties, op5.properties) fun (m0, m1) => ((!((m0.nsw) && (m1.nsw))) && true)
      return (t0, base3, x4, op2, y6, op5))
    (fun (t0, base3, x4, op2, y6, op5) => do
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .shl) #[base3, new8.res[0]!] #[t0] (.inl { nsw := false, nuw := true })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12632
def umin_nuw_shl_common_lhs_dist_nsw : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let base3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[base3, x4] #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .shl) #[base3, y6] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umin) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireEitherOperandOneUse op1.op
      let () ← MatchProg.matchNative (op2.properties, op5.properties) fun (m0, m1) => (((m0.nsw) && (m1.nsw)) && true)
      return (t0, base3, x4, op2, y6, op5))
    (fun (t0, base3, x4, op2, y6, op5) => do
      let new8 ← CreateProg.operation (.llvm .intr__umin) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .shl) #[base3, new8.res[0]!] #[t0] (.inl { nsw := true, nuw := true })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12634
def umax_nuw_shl_common_lhs_dist : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let base3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[base3, x4] #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .shl) #[base3, y6] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireEitherOperandOneUse op1.op
      let () ← MatchProg.matchNative (op2.properties, op5.properties) fun (m0, m1) => ((!((m0.nsw) && (m1.nsw))) && true)
      return (t0, base3, x4, op2, y6, op5))
    (fun (t0, base3, x4, op2, y6, op5) => do
      let new8 ← CreateProg.operation (.llvm .intr__umax) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .shl) #[base3, new8.res[0]!] #[t0] (.inl { nsw := false, nuw := true })
      return new7.res[0]!)
    (fun result => result)

-- InstCombineSimplifyRules.td:12634
def umax_nuw_shl_common_lhs_dist_nsw : Array (CompiledPattern OpCode) :=
  compileVariants 1 fun swaps => Pattern.Builder
    (do
      let t0 ← MatchProg.type (Attr := IntegerType) (fun t => t.bitwidth > 0)
      let base3 ← MatchProg.value t0
      let x4 ← MatchProg.value t0
      let op2 ← MatchProg.operation (.llvm .shl) #[base3, x4] #[t0] (fun p => p.nuw)
      let y6 ← MatchProg.value t0
      let op5 ← MatchProg.operation (.llvm .shl) #[base3, y6] #[t0] (fun p => p.nuw)
      let op1 ← MatchProg.root (.llvm .intr__umax) (orient swaps 0 op2.res[0]! op5.res[0]!) #[t0]
      let () ← requireEitherOperandOneUse op1.op
      let () ← MatchProg.matchNative (op2.properties, op5.properties) fun (m0, m1) => (((m0.nsw) && (m1.nsw)) && true)
      return (t0, base3, x4, op2, y6, op5))
    (fun (t0, base3, x4, op2, y6, op5) => do
      let new8 ← CreateProg.operation (.llvm .intr__umax) #[x4, y6] #[t0]
      let new7 ← CreateProg.operation (.llvm .shl) #[base3, new8.res[0]!] #[t0] (.inl { nsw := true, nuw := true })
      return new7.res[0]!)
    (fun result => result)

/-- Imported families in textual source order. -/
def namedPatterns : Array (String × Array (CompiledPattern OpCode)) := #[
    ("erase_zero_length_memory_intrinsic", erase_zero_length_memory_intrinsic),
    ("reconstruct_two_element_aggregate", reconstruct_two_element_aggregate),
    ("extract_value_from_identical_aggregate_insert_path", extract_value_from_identical_aggregate_insert_path),
    ("extract_prefix_of_aggregate_insert_path", extract_prefix_of_aggregate_insert_path),
    ("aggregate_insert_path_prefix_of_extract", aggregate_insert_path_prefix_of_extract),
    ("bypass_aggregate_insert_on_diverging_extract_path", bypass_aggregate_insert_on_diverging_extract_path),
    ("select_poison_cond", select_poison_cond),
    ("nsw_mul_neg_one", nsw_mul_neg_one),
    ("mul_neg_one", mul_neg_one),
    ("sdiv_neg_one", sdiv_neg_one),
    ("srem_neg_one", srem_neg_one),
    ("and_two_same_masks_drop_one", and_two_same_masks_drop_one),
    ("or_not_and3_contains", or_not_and3_contains),
    ("or_not_and4_contains", or_not_and4_contains),
    ("and_not_or3_contains", and_not_or3_contains),
    ("and_not_or4_contains", and_not_or4_contains),
    ("select_true", select_true),
    ("select_false", select_false),
    ("select_same", select_same),
    ("add_i1_to_xor", add_i1_to_xor),
    ("sub_i1_to_xor", sub_i1_to_xor),
    ("mul_i1_to_and", mul_i1_to_and),
    ("select_true_false", select_true_false),
    ("umax_shl_nuw_scale_inc", umax_shl_nuw_scale_inc),
    ("umax_shl_nuw_scale_inc_commuted", umax_shl_nuw_scale_inc_commuted),
    ("umax_mul_nuw_scale_inc", umax_mul_nuw_scale_inc),
    ("umax_mul_nuw_scale_inc_commuted", umax_mul_nuw_scale_inc_commuted),
    ("umin_i1", umin_i1),
    ("umax_i1", umax_i1),
    ("smin_i1", smin_i1),
    ("smax_i1", smax_i1),
    ("select_eq_zero_self", select_eq_zero_self),
    ("select_ne_zero_self", select_ne_zero_self),
    ("shl_oob_poison", shl_oob_poison),
    ("lshr_oob_poison", lshr_oob_poison),
    ("ashr_oob_poison", ashr_oob_poison),
    ("select_sgt_const_and_to_and_smin", select_sgt_const_and_to_and_smin),
    ("select_sgt_negative_const_xor_signbit_to_and_smin", select_sgt_negative_const_xor_signbit_to_and_smin),
    ("select_ult_and_const_to_and_umin", select_ult_and_const_to_and_umin),
    ("select_sgt_nsw_add_const_to_smax_nsw_add", select_sgt_nsw_add_const_to_smax_nsw_add),
    ("select_slt_nsw_add_const_to_smin_nsw_add", select_slt_nsw_add_const_to_smin_nsw_add),
    ("select_sgt_add_const_to_smax_add", select_sgt_add_const_to_smax_add),
    ("select_slt_add_const_to_smin_add", select_slt_add_const_to_smin_add),
    ("select_ult_add_const_to_umin_add", select_ult_add_const_to_umin_add),
    ("select_ugt_add_const_to_umax_add", select_ugt_add_const_to_umax_add),
    ("select_sgt_const_nsw_nuw_add_to_smin_nsw_nuw_add", select_sgt_const_nsw_nuw_add_to_smin_nsw_nuw_add),
    ("select_sgt_const_nsw_nuw_add_to_smin_nuw_add", select_sgt_const_nsw_nuw_add_to_smin_nuw_add),
    ("select_sgt_const_nsw_nuw_add_to_smin_nsw_add", select_sgt_const_nsw_nuw_add_to_smin_nsw_add),
    ("select_sgt_const_add_to_smin_add", select_sgt_const_add_to_smin_add),
    ("select_ugt_const_add_to_umin_add", select_ugt_const_add_to_umin_add),
    ("select_ugt_const_mul_to_umin_mul", select_ugt_const_mul_to_umin_mul),
    ("select_ult_const_nsw_nuw_mul_to_umax_nsw_nuw_mul", select_ult_const_nsw_nuw_mul_to_umax_nsw_nuw_mul),
    ("select_ult_const_nsw_nuw_mul_to_umax_nuw_mul", select_ult_const_nsw_nuw_mul_to_umax_nuw_mul),
    ("select_ult_const_nsw_nuw_mul_to_umax_nsw_mul", select_ult_const_nsw_nuw_mul_to_umax_nsw_mul),
    ("add_nsw_smin_saturation_bound_to_sadd_sat", add_nsw_smin_saturation_bound_to_sadd_sat),
    ("or_smax_adjacent_equal_endpoints_raise_bound", or_smax_adjacent_equal_endpoints_raise_bound),
    ("select_slt_const_or_to_or_smax", select_slt_const_or_to_or_smax),
    ("select_ugt_const_smin_to_smin_umin", select_ugt_const_smin_to_smin_umin),
    ("select_ugt_const_smax_to_smax_umin", select_ugt_const_smax_to_smax_umin),
    ("select_slt_const_umin_to_umin_smax", select_slt_const_umin_to_umin_smax),
    ("select_sgt_const_umax_to_umax_smin", select_sgt_const_umax_to_umax_smin),
    ("correlated_signed_clamp_lower_less", correlated_signed_clamp_lower_less),
    ("correlated_signed_clamp_lower_greater", correlated_signed_clamp_lower_greater),
    ("correlated_signed_clamp_upper_greater", correlated_signed_clamp_upper_greater),
    ("correlated_signed_clamp_upper_less", correlated_signed_clamp_upper_less),
    ("correlated_unsigned_clamp_lower_less", correlated_unsigned_clamp_lower_less),
    ("correlated_unsigned_clamp_lower_greater", correlated_unsigned_clamp_lower_greater),
    ("correlated_unsigned_clamp_upper_greater", correlated_unsigned_clamp_upper_greater),
    ("correlated_unsigned_clamp_upper_less", correlated_unsigned_clamp_upper_less),
    ("xor_one_use_select_constant_zero_same_constant_true", xor_one_use_select_constant_zero_same_constant_true),
    ("xor_one_use_select_zero_constant_same_constant_false", xor_one_use_select_zero_constant_same_constant_false),
    ("bswap_bswap", bswap_bswap),
    ("bswap_shl_to_single_low_byte", bswap_shl_to_single_low_byte),
    ("bswap_lshr_to_single_high_byte", bswap_lshr_to_single_high_byte),
    ("bswap_shl_leaving_one_byte_to_lshr", bswap_shl_leaving_one_byte_to_lshr),
    ("bswap_lshr_leaving_one_byte_to_shl", bswap_lshr_leaving_one_byte_to_shl),
    ("bswap_and_low_byte_to_shl", bswap_and_low_byte_to_shl),
    ("bswap_and_high_byte_to_lshr", bswap_and_high_byte_to_lshr),
    ("bswap_trunc_bswap_to_high_bytes", bswap_trunc_bswap_to_high_bytes),
    ("select_eq_zero_add_identity", select_eq_zero_add_identity),
    ("xor_pair_common_operand_cancel", xor_pair_common_operand_cancel),
    ("uadd_sat_nested_constants", uadd_sat_nested_constants),
    ("uadd_sat_nested_constants_to_max", uadd_sat_nested_constants_to_max),
    ("usub_sat_nested_constants", usub_sat_nested_constants),
    ("usub_sat_nested_constants_to_zero", usub_sat_nested_constants_to_zero),
    ("sadd_sat_nested_same_sign_constants", sadd_sat_nested_same_sign_constants),
    ("usub_sat_nuw_add_constant_lanes", usub_sat_nuw_add_constant_lanes),
    ("select_eq_pick_rhs", select_eq_pick_rhs),
    ("select_ne_pick_lhs", select_ne_pick_lhs),
    ("smax_smin_val", smax_smin_val),
    ("smin_smax_val", smin_smax_val),
    ("smin_smin_val", smin_smin_val),
    ("smax_smax_val", smax_smax_val),
    ("select_cond_cond_false", select_cond_cond_false),
    ("select_cond_true_cond", select_cond_true_cond),
    ("nuw_add_ugt_self", nuw_add_ugt_self),
    ("nsw_add_neg_slt_self", nsw_add_neg_slt_self),
    ("gep_zero_index", gep_zero_index),
    ("add_select_consts_fold", add_select_consts_fold),
    ("uadd_overflow_zero", uadd_overflow_zero),
    ("uadd_overflow_zero_flag", uadd_overflow_zero_flag),
    ("sadd_overflow_zero", sadd_overflow_zero),
    ("sadd_overflow_zero_flag", sadd_overflow_zero_flag),
    ("usub_overflow_zero", usub_overflow_zero),
    ("usub_overflow_zero_flag", usub_overflow_zero_flag),
    ("ssub_overflow_zero", ssub_overflow_zero),
    ("ssub_overflow_zero_flag", ssub_overflow_zero_flag),
    ("smul_overflow_one", smul_overflow_one),
    ("uadd_overflow_constant_flag", uadd_overflow_constant_flag),
    ("umul_overflow_constant_flag", umul_overflow_constant_flag),
    ("umul_overflow_i1_value", umul_overflow_i1_value),
    ("umul_overflow_i1_flag", umul_overflow_i1_flag),
    ("ssub_overflow_constant_to_sadd", ssub_overflow_constant_to_sadd),
    ("sadd_overflow_minus_one_flag", sadd_overflow_minus_one_flag),
    ("sadd_overflow_positive_constant_flag", sadd_overflow_positive_constant_flag),
    ("sadd_overflow_negative_constant_flag", sadd_overflow_negative_constant_flag),
    ("ssub_overflow_minus_one_flag", ssub_overflow_minus_one_flag),
    ("ssub_overflow_positive_constant_flag", ssub_overflow_positive_constant_flag),
    ("ssub_overflow_negative_constant_flag", ssub_overflow_negative_constant_flag),
    ("ctlz_bitreverse", ctlz_bitreverse),
    ("cttz_bitreverse", cttz_bitreverse),
    ("ctpop_bitreverse", ctpop_bitreverse),
    ("ctpop_bswap", ctpop_bswap),
    ("cttz_neg", cttz_neg),
    ("cttz_abs", cttz_abs),
    ("ctpop_fshl_rotate", ctpop_fshl_rotate),
    ("ctpop_fshr_rotate", ctpop_fshr_rotate),
    ("umin_cttz_cttz", umin_cttz_cttz),
    ("umin_ctlz_ctlz", umin_ctlz_ctlz),
    ("umin_cttz_constant_cap", umin_cttz_constant_cap),
    ("umin_constant_cttz_cap", umin_constant_cttz_cap),
    ("umin_ctlz_constant_cap", umin_ctlz_constant_cap),
    ("umin_constant_ctlz_cap", umin_constant_ctlz_cap),
    ("i_cttz_with_poison_i1_zero_defined", i_cttz_with_poison_i1_zero_defined),
    ("i_ctlz_with_poison_i1_zero_defined", i_ctlz_with_poison_i1_zero_defined),
    ("i_cttz_with_poison_i1_zero_poison", i_cttz_with_poison_i1_zero_poison),
    ("i_ctlz_with_poison_i1_zero_poison", i_ctlz_with_poison_i1_zero_poison),
    ("umin_i_cttz_with_poison_i1_one", umin_i_cttz_with_poison_i1_one),
    ("umin_i_ctlz_with_poison_i1_one", umin_i_ctlz_with_poison_i1_one),
    ("umin_one_i_cttz_with_poison_i1", umin_one_i_cttz_with_poison_i1),
    ("umin_one_i_ctlz_with_poison_i1", umin_one_i_ctlz_with_poison_i1),
    ("brev_dist_i_bswap_and", brev_dist_i_bswap_and),
    ("brev_dist_i_bswap_or", brev_dist_i_bswap_or),
    ("brev_dist_i_bswap_xor", brev_dist_i_bswap_xor),
    ("brev_dist_i_bitreverse_and", brev_dist_i_bitreverse_and),
    ("brev_dist_i_bitreverse_or", brev_dist_i_bitreverse_or),
    ("brev_dist_i_bitreverse_xor", brev_dist_i_bitreverse_xor),
    ("or_bswap_const_distribute", or_bswap_const_distribute),
    ("xor_bswap_const_distribute", xor_bswap_const_distribute),
    ("or_bitreverse_const_distribute", or_bitreverse_const_distribute),
    ("abs_sext_to_zext_abs", abs_sext_to_zext_abs),
    ("fshl_drop_redundant_first_input_mask_for_rotate", fshl_drop_redundant_first_input_mask_for_rotate),
    ("fshl_rotate_exact_low_mask_to_shl", fshl_rotate_exact_low_mask_to_shl),
    ("fshl_drop_noncontributing_masked_second_input", fshl_drop_noncontributing_masked_second_input),
    ("fshl_rotate_or_exact_high_mask", fshl_rotate_or_exact_high_mask),
    ("fshl_zero_lo_to_shl", fshl_zero_lo_to_shl),
    ("fshr_zero_hi_to_lshr", fshr_zero_hi_to_lshr),
    ("fshl_undef_lo_to_shl", fshl_undef_lo_to_shl),
    ("fshr_undef_hi_to_lshr", fshr_undef_hi_to_lshr),
    ("fshl_zero_hi_to_lshr", fshl_zero_hi_to_lshr),
    ("fshl_undef_hi_to_lshr", fshl_undef_hi_to_lshr),
    ("fshr_zero_lo_to_shl", fshr_zero_lo_to_shl),
    ("fshr_undef_lo_to_shl", fshr_undef_lo_to_shl),
    ("ssub_sat_to_sadd_sat", ssub_sat_to_sadd_sat),
    ("smax_nsw_neg_to_neg_smin", smax_nsw_neg_to_neg_smin),
    ("smin_nsw_neg_to_neg_smax", smin_nsw_neg_to_neg_smax),
    ("umin_one_to_zext_ne_zero", umin_one_to_zext_ne_zero),
    ("umax_zext_zext", umax_zext_zext),
    ("umin_zext_zext", umin_zext_zext),
    ("smax_sext_sext", smax_sext_sext),
    ("smin_sext_sext", smin_sext_sext),
    ("extract_smul_ov_neg_one", extract_smul_ov_neg_one),
    ("extract_umul_ov_neg_one", extract_umul_ov_neg_one),
    ("reassoc_const_i_umax", reassoc_const_i_umax),
    ("reassoc_const_i_umin", reassoc_const_i_umin),
    ("reassoc_const_i_smax", reassoc_const_i_smax),
    ("reassoc_const_i_smin", reassoc_const_i_smin),
    ("reassoc_var_const_i_umax", reassoc_var_const_i_umax),
    ("reassoc_var_const_i_umin", reassoc_var_const_i_umin),
    ("reassoc_var_const_i_smax", reassoc_var_const_i_smax),
    ("reassoc_var_const_i_smin", reassoc_var_const_i_smin),
    ("extract_usubo_ov_to_ult", extract_usubo_ov_to_ult),
    ("abs_srem_two", abs_srem_two),
    ("abs_select_neg_x", abs_select_neg_x),
    ("abs_select_x_neg", abs_select_x_neg),
    ("smax_smin_clamp_canon", smax_smin_clamp_canon),
    ("umax_umin_clamp_canon", umax_umin_clamp_canon),
    ("ssub_ov_to_sadd_ov", ssub_ov_to_sadd_ov),
    ("extract_ov1_smul_i1", extract_ov1_smul_i1),
    ("abs_mul_inner_abs", abs_mul_inner_abs),
    ("abs_nsw_mul_inner_abs_plain", abs_nsw_mul_inner_abs_plain),
    ("abs_mul_inner_abs_plain", abs_mul_inner_abs_plain),
    ("abs_nsw_wrapping_mul_inner_abs", abs_nsw_wrapping_mul_inner_abs),
    ("abs_plain_wrapping_mul_inner_abs", abs_plain_wrapping_mul_inner_abs),
    ("i_smax_and_negpow2_factor", i_smax_and_negpow2_factor),
    ("i_smin_and_negpow2_factor", i_smin_and_negpow2_factor),
    ("i_umax_and_negpow2_factor", i_umax_and_negpow2_factor),
    ("i_umin_and_negpow2_factor", i_umin_and_negpow2_factor),
    ("cttz_sext_to_zext", cttz_sext_to_zext),
    ("cttz_zext_zero_poison_narrow", cttz_zext_zero_poison_narrow),
    ("ctpop_zext_narrow", ctpop_zext_narrow),
    ("i_bswap_and_two_i_bswap_cancel", i_bswap_and_two_i_bswap_cancel),
    ("i_bswap_or_two_i_bswap_cancel", i_bswap_or_two_i_bswap_cancel),
    ("i_bswap_xor_two_i_bswap_cancel", i_bswap_xor_two_i_bswap_cancel),
    ("i_bitreverse_and_two_i_bitreverse_cancel", i_bitreverse_and_two_i_bitreverse_cancel),
    ("i_bitreverse_or_two_i_bitreverse_cancel", i_bitreverse_or_two_i_bitreverse_cancel),
    ("i_bitreverse_xor_two_i_bitreverse_cancel", i_bitreverse_xor_two_i_bitreverse_cancel),
    ("bswap_ordered_and_bswap_one_lhs", bswap_ordered_and_bswap_one_lhs),
    ("bswap_ordered_and_bswap_one_rhs", bswap_ordered_and_bswap_one_rhs),
    ("bitrev_ordered_and_bitrev_one_lhs", bitrev_ordered_and_bitrev_one_lhs),
    ("bitrev_ordered_and_bitrev_one_rhs", bitrev_ordered_and_bitrev_one_rhs),
    ("bswap_ordered_or_bswap_one_lhs", bswap_ordered_or_bswap_one_lhs),
    ("bswap_ordered_or_bswap_one_rhs", bswap_ordered_or_bswap_one_rhs),
    ("bitrev_ordered_or_bitrev_one_lhs", bitrev_ordered_or_bitrev_one_lhs),
    ("bitrev_ordered_or_bitrev_one_rhs", bitrev_ordered_or_bitrev_one_rhs),
    ("bswap_ordered_xor_bswap_one_lhs", bswap_ordered_xor_bswap_one_lhs),
    ("bswap_ordered_xor_bswap_one_rhs", bswap_ordered_xor_bswap_one_rhs),
    ("bitrev_ordered_xor_bitrev_one_lhs", bitrev_ordered_xor_bitrev_one_lhs),
    ("bitrev_ordered_xor_bitrev_one_rhs", bitrev_ordered_xor_bitrev_one_rhs),
    ("clamp_smax_smin_two", clamp_smax_smin_two),
    ("clamp_umax_umin_two", clamp_umax_umin_two),
    ("clamp_smin_smax_two", clamp_smin_smax_two),
    ("clamp_umin_umax_two", clamp_umin_umax_two),
    ("umax_nuw_add_dist_common_left", umax_nuw_add_dist_common_left),
    ("umax_nuw_add_dist_common_right", umax_nuw_add_dist_common_right),
    ("umax_nuw_add_dist_crossed_left", umax_nuw_add_dist_crossed_left),
    ("umax_nuw_add_dist_crossed_right", umax_nuw_add_dist_crossed_right),
    ("umin_nuw_add_dist_common_left", umin_nuw_add_dist_common_left),
    ("umin_nuw_add_dist_common_right", umin_nuw_add_dist_common_right),
    ("umin_nuw_add_dist_crossed_left", umin_nuw_add_dist_crossed_left),
    ("umin_nuw_add_dist_crossed_right", umin_nuw_add_dist_crossed_right),
    ("smax_nsw_add_dist_common_left", smax_nsw_add_dist_common_left),
    ("smax_nsw_add_dist_common_right", smax_nsw_add_dist_common_right),
    ("smax_nsw_add_dist_crossed_left", smax_nsw_add_dist_crossed_left),
    ("smax_nsw_add_dist_crossed_right", smax_nsw_add_dist_crossed_right),
    ("smin_nsw_add_dist_common_left", smin_nsw_add_dist_common_left),
    ("smin_nsw_add_dist_common_right", smin_nsw_add_dist_common_right),
    ("smin_nsw_add_dist_crossed_left", smin_nsw_add_dist_crossed_left),
    ("smin_nsw_add_dist_crossed_right", smin_nsw_add_dist_crossed_right),
    ("umax_nuw_add_constant_dist", umax_nuw_add_constant_dist),
    ("umin_nuw_add_constant_dist", umin_nuw_add_constant_dist),
    ("smax_nsw_add_constant_dist", smax_nsw_add_constant_dist),
    ("smin_nsw_add_constant_dist", smin_nsw_add_constant_dist),
    ("umax_nuw_sub_dist", umax_nuw_sub_dist),
    ("umin_nuw_sub_dist", umin_nuw_sub_dist),
    ("smax_nsw_sub_dist", smax_nsw_sub_dist),
    ("smin_nsw_sub_dist", smin_nsw_sub_dist),
    ("cttz_and_neg_self", cttz_and_neg_self),
    ("cttz_umin_one_shl_power_of_two", cttz_umin_one_shl_power_of_two),
    ("ctlz_umin_one_shl_power_of_two", ctlz_umin_one_shl_power_of_two),
    ("cttz_zero_poison_select_shifted_power_of_two_constants", cttz_zero_poison_select_shifted_power_of_two_constants),
    ("extract_smul_ov_pow2", extract_smul_ov_pow2),
    ("extract_umul_ov_pow2", extract_umul_ov_pow2),
    ("extract_umul_self_overflow", extract_umul_self_overflow),
    ("ctlz_lshr_const_zero_poison", ctlz_lshr_const_zero_poison),
    ("cttz_shl_const_zero_poison", cttz_shl_const_zero_poison),
    ("cttz_lowmask_plus1", cttz_lowmask_plus1),
    ("ctpop_or_neg_self", ctpop_or_neg_self),
    ("ctpop_lowclear_mask", ctpop_lowclear_mask),
    ("ctpop_lowbit_minus_one", ctpop_lowbit_minus_one),
    ("ctlz_lowclear_mask", ctlz_lowclear_mask),
    ("fshl_i16_rotate8_to_bswap", fshl_i16_rotate8_to_bswap),
    ("lshr_ctlz_log2bw_to_zext_eq_zero", lshr_ctlz_log2bw_to_zext_eq_zero),
    ("extract0_sole_use_umul_ov", extract0_sole_use_umul_ov),
    ("extract0_sole_use_uadd_ov", extract0_sole_use_uadd_ov),
    ("extract0_sole_use_usub_ov", extract0_sole_use_usub_ov),
    ("extract0_sole_use_sadd_ov", extract0_sole_use_sadd_ov),
    ("extract0_sole_use_ssub_ov", extract0_sole_use_ssub_ov),
    ("extract0_sole_use_smul_ov", extract0_sole_use_smul_ov),
    ("ctpop_lshr_allones", ctpop_lshr_allones),
    ("ctpop_shl_allones", ctpop_shl_allones),
    ("abs_neg_to_abs", abs_neg_to_abs),
    ("smax_opposite_nsw_subtractions_to_nsw_abs", smax_opposite_nsw_subtractions_to_nsw_abs),
    ("smax_opposite_consumed_subtractions_to_abs", smax_opposite_consumed_subtractions_to_abs),
    ("smax_opposite_subtractions_reuse_rhs_as_abs", smax_opposite_subtractions_reuse_rhs_as_abs),
    ("smax_x_neg_x_to_abs", smax_x_neg_x_to_abs),
    ("smin_x_neg_x_to_nabs", smin_x_neg_x_to_nabs),
    ("umin_x_neg_x_to_abs", umin_x_neg_x_to_abs),
    ("umax_x_neg_x_to_nabs", umax_x_neg_x_to_nabs),
    ("umin_nuw_shl_dist", umin_nuw_shl_dist),
    ("umax_nuw_shl_dist", umax_nuw_shl_dist),
    ("fshl_rotate_neg_to_fshr", fshl_rotate_neg_to_fshr),
    ("fshr_rotate_neg_to_fshl", fshr_rotate_neg_to_fshl),
    ("abs_zext_elim", abs_zext_elim),
    ("select_eq_zero_identity", select_eq_zero_identity),
    ("select_ne_zero_identity", select_ne_zero_identity),
    ("select_eq_const_identity", select_eq_const_identity),
    ("select_ne_const_identity", select_ne_const_identity),
    ("select_eq_zero_or", select_eq_zero_or),
    ("select_ne_zero_or", select_ne_zero_or),
    ("reassociate_three_smax_constants", reassociate_three_smax_constants),
    ("reassociate_three_smin_constants", reassociate_three_smin_constants),
    ("reassociate_three_umax_constants", reassociate_three_umax_constants),
    ("reassociate_three_umin_constants", reassociate_three_umin_constants),
    ("smax_smax_const_fold", smax_smax_const_fold),
    ("smin_smin_const_fold", smin_smin_const_fold),
    ("umax_umax_const_fold", umax_umax_const_fold),
    ("umin_umin_const_fold", umin_umin_const_fold),
    ("umax_smax_nonnegative_constants_fold", umax_smax_nonnegative_constants_fold),
    ("smin_umin_nonnegative_constants_fold", smin_umin_nonnegative_constants_fold),
    ("bitreverse_zext_i1_to_select", bitreverse_zext_i1_to_select),
    ("bitreverse_zext_i1_not_sign_extract", bitreverse_zext_i1_not_sign_extract),
    ("bitreverse_i1_select_not_sign_extract", bitreverse_i1_select_not_sign_extract),
    ("usub_sat_nuwsub_const", usub_sat_nuwsub_const),
    ("select_nested_same_cond_false", select_nested_same_cond_false),
    ("select_nested_same_cond_true", select_nested_same_cond_true),
    ("usub_sat_nuwsub_constant_lanes", usub_sat_nuwsub_constant_lanes),
    ("usub_sat_select_one_zext_not_condition", usub_sat_select_one_zext_not_condition),
    ("umin_nuw_shl_common_lhs_dist", umin_nuw_shl_common_lhs_dist),
    ("umin_nuw_shl_common_lhs_dist_nsw", umin_nuw_shl_common_lhs_dist_nsw),
    ("umax_nuw_shl_common_lhs_dist", umax_nuw_shl_common_lhs_dist),
    ("umax_nuw_shl_common_lhs_dist_nsw", umax_nuw_shl_common_lhs_dist_nsw)]

/-- Opcode dispatch preserves source order within each applicable bucket. -/
private def rewritesFor : Llvm → RewritePattern OpCode
  | .intr__memcpy => RewritePattern.GreedyRewritePattern (#[
      erase_zero_length_memory_intrinsic].flatten.map (·.run))
  | .intr__memmove => RewritePattern.GreedyRewritePattern (#[
      erase_zero_length_memory_intrinsic].flatten.map (·.run))
  | .intr__memset => RewritePattern.GreedyRewritePattern (#[
      erase_zero_length_memory_intrinsic].flatten.map (·.run))
  | .insertvalue => RewritePattern.GreedyRewritePattern (#[
      reconstruct_two_element_aggregate].flatten.map (·.run))
  | .extractvalue => RewritePattern.GreedyRewritePattern (#[
      extract_value_from_identical_aggregate_insert_path,
      extract_prefix_of_aggregate_insert_path,
      aggregate_insert_path_prefix_of_extract,
      bypass_aggregate_insert_on_diverging_extract_path,
      uadd_overflow_zero,
      uadd_overflow_zero_flag,
      sadd_overflow_zero,
      sadd_overflow_zero_flag,
      usub_overflow_zero,
      usub_overflow_zero_flag,
      ssub_overflow_zero,
      ssub_overflow_zero_flag,
      smul_overflow_one,
      uadd_overflow_constant_flag,
      umul_overflow_constant_flag,
      umul_overflow_i1_value,
      umul_overflow_i1_flag,
      sadd_overflow_minus_one_flag,
      sadd_overflow_positive_constant_flag,
      sadd_overflow_negative_constant_flag,
      ssub_overflow_minus_one_flag,
      ssub_overflow_positive_constant_flag,
      ssub_overflow_negative_constant_flag,
      extract_smul_ov_neg_one,
      extract_umul_ov_neg_one,
      extract_usubo_ov_to_ult,
      extract_ov1_smul_i1,
      extract_smul_ov_pow2,
      extract_umul_ov_pow2,
      extract_umul_self_overflow,
      extract0_sole_use_umul_ov,
      extract0_sole_use_uadd_ov,
      extract0_sole_use_usub_ov,
      extract0_sole_use_sadd_ov,
      extract0_sole_use_ssub_ov,
      extract0_sole_use_smul_ov].flatten.map (·.run))
  | .select => RewritePattern.GreedyRewritePattern (#[
      select_poison_cond,
      select_true,
      select_false,
      select_same,
      select_true_false,
      select_eq_zero_self,
      select_ne_zero_self,
      select_sgt_const_and_to_and_smin,
      select_sgt_negative_const_xor_signbit_to_and_smin,
      select_ult_and_const_to_and_umin,
      select_sgt_nsw_add_const_to_smax_nsw_add,
      select_slt_nsw_add_const_to_smin_nsw_add,
      select_sgt_add_const_to_smax_add,
      select_slt_add_const_to_smin_add,
      select_ult_add_const_to_umin_add,
      select_ugt_add_const_to_umax_add,
      select_sgt_const_nsw_nuw_add_to_smin_nsw_nuw_add,
      select_sgt_const_nsw_nuw_add_to_smin_nuw_add,
      select_sgt_const_nsw_nuw_add_to_smin_nsw_add,
      select_sgt_const_add_to_smin_add,
      select_ugt_const_add_to_umin_add,
      select_ugt_const_mul_to_umin_mul,
      select_ult_const_nsw_nuw_mul_to_umax_nsw_nuw_mul,
      select_ult_const_nsw_nuw_mul_to_umax_nuw_mul,
      select_ult_const_nsw_nuw_mul_to_umax_nsw_mul,
      select_slt_const_or_to_or_smax,
      select_ugt_const_smin_to_smin_umin,
      select_ugt_const_smax_to_smax_umin,
      select_slt_const_umin_to_umin_smax,
      select_sgt_const_umax_to_umax_smin,
      correlated_signed_clamp_lower_less,
      correlated_signed_clamp_lower_greater,
      correlated_signed_clamp_upper_greater,
      correlated_signed_clamp_upper_less,
      correlated_unsigned_clamp_lower_less,
      correlated_unsigned_clamp_lower_greater,
      correlated_unsigned_clamp_upper_greater,
      correlated_unsigned_clamp_upper_less,
      select_eq_zero_add_identity,
      select_eq_pick_rhs,
      select_ne_pick_lhs,
      select_cond_cond_false,
      select_cond_true_cond,
      select_eq_zero_identity,
      select_ne_zero_identity,
      select_eq_const_identity,
      select_ne_const_identity,
      select_eq_zero_or,
      select_ne_zero_or,
      select_nested_same_cond_false,
      select_nested_same_cond_true].flatten.map (·.run))
  | .mul => RewritePattern.GreedyRewritePattern (#[
      nsw_mul_neg_one,
      mul_neg_one,
      mul_i1_to_and].flatten.map (·.run))
  | .sdiv => RewritePattern.GreedyRewritePattern (#[
      sdiv_neg_one].flatten.map (·.run))
  | .srem => RewritePattern.GreedyRewritePattern (#[
      srem_neg_one].flatten.map (·.run))
  | .and => RewritePattern.GreedyRewritePattern (#[
      and_two_same_masks_drop_one,
      and_not_or3_contains,
      and_not_or4_contains,
      brev_dist_i_bswap_and,
      brev_dist_i_bitreverse_and].flatten.map (·.run))
  | .or => RewritePattern.GreedyRewritePattern (#[
      or_not_and3_contains,
      or_not_and4_contains,
      or_smax_adjacent_equal_endpoints_raise_bound,
      brev_dist_i_bswap_or,
      brev_dist_i_bitreverse_or,
      or_bswap_const_distribute,
      or_bitreverse_const_distribute].flatten.map (·.run))
  | .add => RewritePattern.GreedyRewritePattern (#[
      add_i1_to_xor,
      add_nsw_smin_saturation_bound_to_sadd_sat,
      add_select_consts_fold].flatten.map (·.run))
  | .sub => RewritePattern.GreedyRewritePattern (#[
      sub_i1_to_xor].flatten.map (·.run))
  | .intr__umax => RewritePattern.GreedyRewritePattern (#[
      umax_shl_nuw_scale_inc,
      umax_shl_nuw_scale_inc_commuted,
      umax_mul_nuw_scale_inc,
      umax_mul_nuw_scale_inc_commuted,
      umax_i1,
      umax_zext_zext,
      reassoc_const_i_umax,
      reassoc_var_const_i_umax,
      umax_umin_clamp_canon,
      i_umax_and_negpow2_factor,
      clamp_umax_umin_two,
      umax_nuw_add_dist_common_left,
      umax_nuw_add_dist_common_right,
      umax_nuw_add_dist_crossed_left,
      umax_nuw_add_dist_crossed_right,
      umax_nuw_add_constant_dist,
      umax_nuw_sub_dist,
      umax_x_neg_x_to_nabs,
      umax_nuw_shl_dist,
      reassociate_three_umax_constants,
      umax_umax_const_fold,
      umax_smax_nonnegative_constants_fold,
      umax_nuw_shl_common_lhs_dist,
      umax_nuw_shl_common_lhs_dist_nsw].flatten.map (·.run))
  | .intr__umin => RewritePattern.GreedyRewritePattern (#[
      umin_i1,
      umin_cttz_cttz,
      umin_ctlz_ctlz,
      umin_cttz_constant_cap,
      umin_constant_cttz_cap,
      umin_ctlz_constant_cap,
      umin_constant_ctlz_cap,
      umin_i_cttz_with_poison_i1_one,
      umin_i_ctlz_with_poison_i1_one,
      umin_one_i_cttz_with_poison_i1,
      umin_one_i_ctlz_with_poison_i1,
      umin_one_to_zext_ne_zero,
      umin_zext_zext,
      reassoc_const_i_umin,
      reassoc_var_const_i_umin,
      i_umin_and_negpow2_factor,
      clamp_umin_umax_two,
      umin_nuw_add_dist_common_left,
      umin_nuw_add_dist_common_right,
      umin_nuw_add_dist_crossed_left,
      umin_nuw_add_dist_crossed_right,
      umin_nuw_add_constant_dist,
      umin_nuw_sub_dist,
      umin_x_neg_x_to_abs,
      umin_nuw_shl_dist,
      reassociate_three_umin_constants,
      umin_umin_const_fold,
      umin_nuw_shl_common_lhs_dist,
      umin_nuw_shl_common_lhs_dist_nsw].flatten.map (·.run))
  | .intr__smin => RewritePattern.GreedyRewritePattern (#[
      smin_i1,
      smin_smax_val,
      smin_smin_val,
      smin_nsw_neg_to_neg_smax,
      smin_sext_sext,
      reassoc_const_i_smin,
      reassoc_var_const_i_smin,
      i_smin_and_negpow2_factor,
      clamp_smin_smax_two,
      smin_nsw_add_dist_common_left,
      smin_nsw_add_dist_common_right,
      smin_nsw_add_dist_crossed_left,
      smin_nsw_add_dist_crossed_right,
      smin_nsw_add_constant_dist,
      smin_nsw_sub_dist,
      smin_x_neg_x_to_nabs,
      reassociate_three_smin_constants,
      smin_smin_const_fold,
      smin_umin_nonnegative_constants_fold].flatten.map (·.run))
  | .intr__smax => RewritePattern.GreedyRewritePattern (#[
      smax_i1,
      smax_smin_val,
      smax_smax_val,
      smax_nsw_neg_to_neg_smin,
      smax_sext_sext,
      reassoc_const_i_smax,
      reassoc_var_const_i_smax,
      smax_smin_clamp_canon,
      i_smax_and_negpow2_factor,
      clamp_smax_smin_two,
      smax_nsw_add_dist_common_left,
      smax_nsw_add_dist_common_right,
      smax_nsw_add_dist_crossed_left,
      smax_nsw_add_dist_crossed_right,
      smax_nsw_add_constant_dist,
      smax_nsw_sub_dist,
      smax_opposite_nsw_subtractions_to_nsw_abs,
      smax_opposite_consumed_subtractions_to_abs,
      smax_opposite_subtractions_reuse_rhs_as_abs,
      smax_x_neg_x_to_abs,
      reassociate_three_smax_constants,
      smax_smax_const_fold].flatten.map (·.run))
  | .shl => RewritePattern.GreedyRewritePattern (#[
      shl_oob_poison].flatten.map (·.run))
  | .lshr => RewritePattern.GreedyRewritePattern (#[
      lshr_oob_poison,
      lshr_ctlz_log2bw_to_zext_eq_zero].flatten.map (·.run))
  | .ashr => RewritePattern.GreedyRewritePattern (#[
      ashr_oob_poison].flatten.map (·.run))
  | .xor => RewritePattern.GreedyRewritePattern (#[
      xor_one_use_select_constant_zero_same_constant_true,
      xor_one_use_select_zero_constant_same_constant_false,
      xor_pair_common_operand_cancel,
      brev_dist_i_bswap_xor,
      brev_dist_i_bitreverse_xor,
      xor_bswap_const_distribute].flatten.map (·.run))
  | .intr__bswap => RewritePattern.GreedyRewritePattern (#[
      bswap_bswap,
      bswap_shl_to_single_low_byte,
      bswap_lshr_to_single_high_byte,
      bswap_shl_leaving_one_byte_to_lshr,
      bswap_lshr_leaving_one_byte_to_shl,
      bswap_and_low_byte_to_shl,
      bswap_and_high_byte_to_lshr,
      bswap_trunc_bswap_to_high_bytes,
      i_bswap_and_two_i_bswap_cancel,
      i_bswap_or_two_i_bswap_cancel,
      i_bswap_xor_two_i_bswap_cancel,
      bswap_ordered_and_bswap_one_lhs,
      bswap_ordered_and_bswap_one_rhs,
      bswap_ordered_or_bswap_one_lhs,
      bswap_ordered_or_bswap_one_rhs,
      bswap_ordered_xor_bswap_one_lhs,
      bswap_ordered_xor_bswap_one_rhs].flatten.map (·.run))
  | .intr__uadd__sat => RewritePattern.GreedyRewritePattern (#[
      uadd_sat_nested_constants,
      uadd_sat_nested_constants_to_max].flatten.map (·.run))
  | .intr__usub__sat => RewritePattern.GreedyRewritePattern (#[
      usub_sat_nested_constants,
      usub_sat_nested_constants_to_zero,
      usub_sat_nuw_add_constant_lanes,
      usub_sat_nuwsub_const,
      usub_sat_nuwsub_constant_lanes,
      usub_sat_select_one_zext_not_condition].flatten.map (·.run))
  | .intr__sadd__sat => RewritePattern.GreedyRewritePattern (#[
      sadd_sat_nested_same_sign_constants].flatten.map (·.run))
  | .icmp => RewritePattern.GreedyRewritePattern (#[
      nuw_add_ugt_self,
      nsw_add_neg_slt_self].flatten.map (·.run))
  | .getelementptr => RewritePattern.GreedyRewritePattern (#[
      gep_zero_index].flatten.map (·.run))
  | .intr__ssub__with__overflow => RewritePattern.GreedyRewritePattern (#[
      ssub_overflow_constant_to_sadd,
      ssub_ov_to_sadd_ov].flatten.map (·.run))
  | .intr__ctlz => RewritePattern.GreedyRewritePattern (#[
      ctlz_bitreverse,
      i_ctlz_with_poison_i1_zero_defined,
      i_ctlz_with_poison_i1_zero_poison,
      ctlz_umin_one_shl_power_of_two,
      ctlz_lshr_const_zero_poison,
      ctlz_lowclear_mask].flatten.map (·.run))
  | .intr__cttz => RewritePattern.GreedyRewritePattern (#[
      cttz_bitreverse,
      cttz_neg,
      cttz_abs,
      i_cttz_with_poison_i1_zero_defined,
      i_cttz_with_poison_i1_zero_poison,
      cttz_sext_to_zext,
      cttz_zext_zero_poison_narrow,
      cttz_and_neg_self,
      cttz_umin_one_shl_power_of_two,
      cttz_zero_poison_select_shifted_power_of_two_constants,
      cttz_shl_const_zero_poison,
      cttz_lowmask_plus1].flatten.map (·.run))
  | .intr__ctpop => RewritePattern.GreedyRewritePattern (#[
      ctpop_bitreverse,
      ctpop_bswap,
      ctpop_fshl_rotate,
      ctpop_fshr_rotate,
      ctpop_zext_narrow,
      ctpop_or_neg_self,
      ctpop_lowclear_mask,
      ctpop_lowbit_minus_one,
      ctpop_lshr_allones,
      ctpop_shl_allones].flatten.map (·.run))
  | .intr__abs => RewritePattern.GreedyRewritePattern (#[
      abs_sext_to_zext_abs,
      abs_srem_two,
      abs_select_neg_x,
      abs_select_x_neg,
      abs_mul_inner_abs,
      abs_nsw_mul_inner_abs_plain,
      abs_mul_inner_abs_plain,
      abs_nsw_wrapping_mul_inner_abs,
      abs_plain_wrapping_mul_inner_abs,
      abs_neg_to_abs,
      abs_zext_elim].flatten.map (·.run))
  | .intr__fshl => RewritePattern.GreedyRewritePattern (#[
      fshl_drop_redundant_first_input_mask_for_rotate,
      fshl_rotate_exact_low_mask_to_shl,
      fshl_drop_noncontributing_masked_second_input,
      fshl_rotate_or_exact_high_mask,
      fshl_zero_lo_to_shl,
      fshl_undef_lo_to_shl,
      fshl_zero_hi_to_lshr,
      fshl_undef_hi_to_lshr,
      fshl_i16_rotate8_to_bswap,
      fshl_rotate_neg_to_fshr].flatten.map (·.run))
  | .intr__fshr => RewritePattern.GreedyRewritePattern (#[
      fshr_zero_hi_to_lshr,
      fshr_undef_hi_to_lshr,
      fshr_zero_lo_to_shl,
      fshr_undef_lo_to_shl,
      fshr_rotate_neg_to_fshl].flatten.map (·.run))
  | .intr__ssub__sat => RewritePattern.GreedyRewritePattern (#[
      ssub_sat_to_sadd_sat].flatten.map (·.run))
  | .intr__bitreverse => RewritePattern.GreedyRewritePattern (#[
      i_bitreverse_and_two_i_bitreverse_cancel,
      i_bitreverse_or_two_i_bitreverse_cancel,
      i_bitreverse_xor_two_i_bitreverse_cancel,
      bitrev_ordered_and_bitrev_one_lhs,
      bitrev_ordered_and_bitrev_one_rhs,
      bitrev_ordered_or_bitrev_one_lhs,
      bitrev_ordered_or_bitrev_one_rhs,
      bitrev_ordered_xor_bitrev_one_lhs,
      bitrev_ordered_xor_bitrev_one_rhs,
      bitreverse_zext_i1_to_select].flatten.map (·.run))
  | .zext => RewritePattern.GreedyRewritePattern (#[
      bitreverse_zext_i1_not_sign_extract,
      bitreverse_i1_select_not_sign_extract].flatten.map (·.run))
  | _ => fun rewriter _ _ => some rewriter

/-- Try the imported rules without rebuilding compiled patterns. -/
def rewrite : RewritePattern OpCode :=
  fun rewriter op opInBounds =>
    match op.getOpType rewriter.ctx.raw opInBounds with
    | .llvm opcode => rewritesFor opcode rewriter op opInBounds
    | _ => some rewriter

end

end Veir.InstructionSimplify
