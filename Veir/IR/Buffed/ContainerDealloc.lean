module

public import Veir.IR.Buffed.Basic
public import Veir.IR.ContainerDealloc
public import Veir.IR.Buffed.Frames
import all Veir.IR.Buffed.Basic

@[expose] public section
namespace Veir
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000
setup_grind_with_get_set_definitions
attribute [local grind] TopLevelPtr.InBounds
attribute [local grind] Veir.BlockPtr.dealloc Veir.RegionPtr.dealloc

@[grind →]
theorem TopLevelPtr.inBounds_BlockPtr_dealloc_old {ctx : IRContext OpInfo}
    {ptr : Veir.BlockPtr} {p : TopLevelPtr} (h : p.InBounds (ptr.dealloc ctx)) :
    p.InBounds ctx := by
  cases p <;> grind [TopLevelPtr.InBounds]

@[grind →]
theorem TopLevelPtr.inBounds_RegionPtr_dealloc_old {ctx : IRContext OpInfo}
    {ptr : Veir.RegionPtr} {p : TopLevelPtr} (h : p.InBounds (ptr.dealloc ctx)) :
    p.InBounds ctx := by
  cases p <;> grind [TopLevelPtr.InBounds]

private theorem IRContext.isRepr_BlockPtr_dealloc
    {ctx : IRContext OpInfo} (hctx : ctx.IsRepr)
    (op : BlockPtr) (hop : op.InBounds ctx) :
    (op.dealloc ctx).IsRepr := by
  grind [IRContext.IsRepr]

private theorem IRContext.layoutPreserved_BlockPtr_dealloc
    {ctx : IRContext OpInfo} (op : BlockPtr) (hop : op.InBounds ctx) :
    (op.dealloc ctx).LayoutPreserved ctx := by
  constructor <;> grind [OperationPtr.LayoutPreserved, BlockPtr.LayoutPreserved]

private theorem TopLevelPtr.range_BlockPtr_dealloc
    {ctx : IRContext OpInfo} (op : BlockPtr) (hop : op.InBounds ctx)
    (p : TopLevelPtr) (hp : p.InBounds (op.dealloc ctx)) :
    p.range (op.dealloc ctx) = p.range ctx := by
  have hlay := IRContext.layoutPreserved_BlockPtr_dealloc op hop
  cases p with
  | operation op =>
    exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay
  | block block =>
    exact LayoutPreserved.same_blockPtr_range block (by simpa using hp) hlay
  | region => rfl

private theorem OpOperandPtr.matches_BlockPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.BlockPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (oper : OpOperandPtr) (hib : oper.InBounds (ptr.spec.dealloc ctx.spec)) :
    oper.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_BlockPtr_dealloc ptr.spec ib.ib
  have hib' : oper.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op oper.op (by grind) |>.operands oper hib' rfl
  have hfib := OpOperandPtr.get_fieldsInBounds spec' oper fib hib
  have htoM := OpOperandPtr.layoutPreserved_same_toM hlay hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := OpOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have htoM_v := ValuePtr.layoutPreserved_same_toM hlay hfib.value_inBounds
  have hget : oper.get! spec' = oper.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.nextUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readNextUse!]
  · have := hm.back
    rw [Sim.OpOperandPtrPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readBack!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readOwner!]
  · have := hm.value
    rw [Sim.ValuePtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readValue!]

private theorem BlockOperandPtr.matches_BlockPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.BlockPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (oper : BlockOperandPtr) (hib : oper.InBounds (ptr.spec.dealloc ctx.spec)) :
    oper.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_BlockPtr_dealloc ptr.spec ib.ib
  have hib' : oper.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op oper.op (by grind) |>.blockOperands oper hib' rfl
  have hfib := BlockOperandPtr.get_fieldsInBounds spec' oper fib hib
  have htoM := BlockOperandPtr.layoutPreserved_same_toM hlay hib
  have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := BlockOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have hget : oper.get! spec' = oper.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.nextUse
    rw [Sim.OptionBlockOperandPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readNextUse!]
  · have := hm.back
    rw [Sim.BlockOperandPtrPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readBack!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readOwner!]
  · have := hm.value
    rw [Sim.BlockPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readValue!]

private theorem OpResultPtr.matches_BlockPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.BlockPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (res : OpResultPtr) (hib : res.InBounds (ptr.spec.dealloc ctx.spec)) :
    res.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_BlockPtr_dealloc ptr.spec ib.ib
  have hib' : res.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op res.op (by grind) |>.results res hib' rfl
  have hfib := OpResultPtr.get_fieldsInBounds spec' res fib hib
  have htoM := OpResultPtr.layoutPreserved_same_toM hlay hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have hget : res.get! spec' = res.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.kind
    grind [Buffed.OpResultMPtr.readKind!]
  · have := hm.typee
    grind [Buffed.OpResultMPtr.readType!]
  · have := hm.firstUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.OpResultMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.OpResultMPtr.readIndex!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.OpResultMPtr.readOwner!]

private theorem BlockArgumentPtr.matches_BlockPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.BlockPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (arg : BlockArgumentPtr) (hib : arg.InBounds (ptr.spec.dealloc ctx.spec)) :
    arg.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_BlockPtr_dealloc ptr.spec ib.ib
  have hib' : arg.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_block arg.block (by grind) |>.arguments arg hib' rfl
  have hfib := BlockArgumentPtr.get_fieldsInBounds spec' arg fib hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have hget : arg.get! spec' = arg.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.kind
    grind [Buffed.BlockArgumentMPtr.readKind!]
  · have := hm.type
    grind [Buffed.BlockArgumentMPtr.readType!]
  · have := hm.firstUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.BlockArgumentMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.BlockArgumentMPtr.readIndex!]
  · have := hm.owner
    rw [Sim.BlockPtr.Sim_def] at this ⊢
    grind [Buffed.BlockArgumentMPtr.readOwner!]

buffed (inline := true)
def Sim.BlockPtr.forgetSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds := by grind) : Sim.IRContext OpInfo :=
  ⟨ctx.buf,
   (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.dealloc ctx),
   by
     simp only [Erased.map_mk]
     constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
     case fieldsInBounds => exact fib
     case repr => exact IRContext.isRepr_BlockPtr_dealloc ctx.sim.repr ptr.spec ib.ib
     case in_bounds =>
       intro p hp
       rw [TopLevelPtr.range_BlockPtr_dealloc ptr.spec ib.ib p hp]
       exact ctx.sim.in_bounds p (by grind)
     case disjoint_allocs =>
       intro p₁ p₂ hp₁ hp₂ hne
       rw [TopLevelPtr.range_BlockPtr_dealloc ptr.spec ib.ib p₁ hp₁,
         TopLevelPtr.range_BlockPtr_dealloc ptr.spec ib.ib p₂ hp₂]
       exact ctx.sim.disjoint_allocs p₁ p₂ (by grind) (by grind) hne
     case encoding_op =>
       intro op hop
       have hop' : op.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_op op hop'
       have hget : op.get! (ptr.spec.dealloc ctx.spec) = op.get! ctx.spec := by grind
       have htype : op.getOpType! (ptr.spec.dealloc ctx.spec) = op.getOpType! ctx.spec := by grind [Veir.OperationPtr.getOpType!]
       have hprops : op.getProperties! (ptr.spec.dealloc ctx.spec)
           (op.getOpType! ctx.spec) = op.getProperties! ctx.spec (op.getOpType! ctx.spec) := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · have := henc.prev; grind
         · have := henc.next; grind
         · have := henc.parent; grind
         · have := henc.opType; grind
         · change ctx.buf.attributes[(Buffed.OperationMPtr.readAttrs! ctx.buf op.toM).toNat]? =
             some (op.get! (ptr.spec.dealloc ctx.spec)).attrs
           rw [hget]
           exact henc.attrs
         · rw [Erased.out_mk, htype, hprops]
           exact henc.props
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numBlockOperands
         · intro bo hbo _
           exact BlockOperandPtr.matches_BlockPtr_dealloc ptr ib fib bo hbo
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numRegions
         · intro idx hidx
           have hnum : op.getNumRegions! (ptr.spec.dealloc ctx.spec) =
               op.getNumRegions! ctx.spec := by grind
           have hreg : op.getRegion! (ptr.spec.dealloc ctx.spec) idx =
               op.getRegion! ctx.spec idx := by grind
           rw [hreg]
           exact henc.regions idx (by grind)
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numOperands
         · intro oper hoper _
           exact OpOperandPtr.matches_BlockPtr_dealloc ptr ib fib oper hoper
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numResults
         · intro res hres _
           exact OpResultPtr.matches_BlockPtr_dealloc ptr ib fib res hres
     case encoding_block =>
       intro block hblock
       have hblock' : block.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_block block hblock'
       have hget : block.get! (ptr.spec.dealloc ctx.spec) = block.get! ctx.spec := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
       · have hfib := BlockPtr.get_fieldsInBounds _ block fib hblock
         have hlay := IRContext.layoutPreserved_BlockPtr_dealloc ptr.spec ib.ib
         have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay
           ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
         constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · have := henc.firstUse
           rw [Sim.OptionBlockOperandPtr.Sim_def] at this ⊢
           grind
         · have := henc.prev; grind
         · have := henc.next; grind
         · have := henc.parent; grind
         · have := henc.firstOp; grind
         · have := henc.lastOp; grind
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numArguments
         · intro arg harg _
           exact BlockArgumentPtr.matches_BlockPtr_dealloc ptr ib fib arg harg
     case encoding_region =>
       intro region hregion
       have hregion' : region.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_region region hregion'
       have hget : region.get! (ptr.spec.dealloc ctx.spec) = region.get! ctx.spec := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
       · have := henc.firstBlock; grind
       · have := henc.lastBlock; grind
       · have := henc.parent; grind
     case attr_empty => exact ctx.sim.attr_empty⟩


private theorem IRContext.isRepr_RegionPtr_dealloc
    {ctx : IRContext OpInfo} (hctx : ctx.IsRepr)
    (op : RegionPtr) (hop : op.InBounds ctx) :
    (op.dealloc ctx).IsRepr := by
  grind [IRContext.IsRepr]

private theorem IRContext.layoutPreserved_RegionPtr_dealloc
    {ctx : IRContext OpInfo} (op : RegionPtr) (hop : op.InBounds ctx) :
    (op.dealloc ctx).LayoutPreserved ctx := by
  constructor <;> grind [OperationPtr.LayoutPreserved, BlockPtr.LayoutPreserved]

private theorem TopLevelPtr.range_RegionPtr_dealloc
    {ctx : IRContext OpInfo} (op : RegionPtr) (hop : op.InBounds ctx)
    (p : TopLevelPtr) (hp : p.InBounds (op.dealloc ctx)) :
    p.range (op.dealloc ctx) = p.range ctx := by
  have hlay := IRContext.layoutPreserved_RegionPtr_dealloc op hop
  cases p with
  | operation op =>
    exact LayoutPreserved.same_operationPtr_range op (by simpa using hp) hlay
  | block block =>
    exact LayoutPreserved.same_blockPtr_range block (by simpa using hp) hlay
  | region => rfl

private theorem OpOperandPtr.matches_RegionPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (oper : OpOperandPtr) (hib : oper.InBounds (ptr.spec.dealloc ctx.spec)) :
    oper.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_RegionPtr_dealloc ptr.spec ib.ib
  have hib' : oper.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op oper.op (by grind) |>.operands oper hib' rfl
  have hfib := OpOperandPtr.get_fieldsInBounds spec' oper fib hib
  have htoM := OpOperandPtr.layoutPreserved_same_toM hlay hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := OpOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have htoM_v := ValuePtr.layoutPreserved_same_toM hlay hfib.value_inBounds
  have hget : oper.get! spec' = oper.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.nextUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readNextUse!]
  · have := hm.back
    rw [Sim.OpOperandPtrPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readBack!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readOwner!]
  · have := hm.value
    rw [Sim.ValuePtr.Sim_def] at this ⊢
    grind [Buffed.OpOperandMPtr.readValue!]

private theorem BlockOperandPtr.matches_RegionPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (oper : BlockOperandPtr) (hib : oper.InBounds (ptr.spec.dealloc ctx.spec)) :
    oper.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_RegionPtr_dealloc ptr.spec ib.ib
  have hib' : oper.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op oper.op (by grind) |>.blockOperands oper hib' rfl
  have hfib := BlockOperandPtr.get_fieldsInBounds spec' oper fib hib
  have htoM := BlockOperandPtr.layoutPreserved_same_toM hlay hib
  have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.nextUse_inBounds)
  have htoM_b := BlockOperandPtrPtr.layoutPreserved_same_toM hlay hfib.back_inBounds
  have hget : oper.get! spec' = oper.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.nextUse
    rw [Sim.OptionBlockOperandPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readNextUse!]
  · have := hm.back
    rw [Sim.BlockOperandPtrPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readBack!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readOwner!]
  · have := hm.value
    rw [Sim.BlockPtr.Sim_def] at this ⊢
    grind [Buffed.BlockOperandMPtr.readValue!]

private theorem OpResultPtr.matches_RegionPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (res : OpResultPtr) (hib : res.InBounds (ptr.spec.dealloc ctx.spec)) :
    res.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_RegionPtr_dealloc ptr.spec ib.ib
  have hib' : res.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_op res.op (by grind) |>.results res hib' rfl
  have hfib := OpResultPtr.get_fieldsInBounds spec' res fib hib
  have htoM := OpResultPtr.layoutPreserved_same_toM hlay hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have hget : res.get! spec' = res.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.kind
    grind [Buffed.OpResultMPtr.readKind!]
  · have := hm.typee
    grind [Buffed.OpResultMPtr.readType!]
  · have := hm.firstUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.OpResultMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.OpResultMPtr.readIndex!]
  · have := hm.owner
    rw [Sim.OperationPtr.Sim_def] at this ⊢
    grind [Buffed.OpResultMPtr.readOwner!]

private theorem BlockArgumentPtr.matches_RegionPtr_dealloc
    {ctx : Sim.IRContext OpInfo} (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds)
    (arg : BlockArgumentPtr) (hib : arg.InBounds (ptr.spec.dealloc ctx.spec)) :
    arg.Matches { buf := ctx.buf, spec' := .mk (ptr.spec.dealloc ctx.spec) } (by grind) := by
  let spec' := ptr.spec.dealloc ctx.spec
  have hlay : spec'.LayoutPreserved ctx.spec :=
    IRContext.layoutPreserved_RegionPtr_dealloc ptr.spec ib.ib
  have hib' : arg.InBounds ctx.spec := by grind
  have hm := ctx.sim.encoding_block arg.block (by grind) |>.arguments arg hib' rfl
  have hfib := BlockArgumentPtr.get_fieldsInBounds spec' arg fib hib
  have htoO := OpOperandPtr.layoutPreserved_same_toO hlay
    ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
  have hget : arg.get! spec' = arg.get! ctx.spec := by grind
  constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
  · have := hm.kind
    grind [Buffed.BlockArgumentMPtr.readKind!]
  · have := hm.type
    grind [Buffed.BlockArgumentMPtr.readType!]
  · have := hm.firstUse
    rw [Sim.OptionOpOperandPtr.Sim_def] at this ⊢
    grind [Buffed.BlockArgumentMPtr.readFirstUse!]
  · have := hm.index
    grind [Buffed.BlockArgumentMPtr.readIndex!]
  · have := hm.owner
    rw [Sim.BlockPtr.Sim_def] at this ⊢
    grind [Buffed.BlockArgumentMPtr.readOwner!]

buffed (inline := true)
def Sim.RegionPtr.forgetSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx)
    (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds := by grind) : Sim.IRContext OpInfo :=
  ⟨ctx.buf,
   (Erased.mk (ptr.spec, ctx.spec)).map (fun (ptr, ctx) => ptr.dealloc ctx),
   by
     simp only [Erased.map_mk]
     constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
     case fieldsInBounds => exact fib
     case repr => exact IRContext.isRepr_RegionPtr_dealloc ctx.sim.repr ptr.spec ib.ib
     case in_bounds =>
       intro p hp
       rw [TopLevelPtr.range_RegionPtr_dealloc ptr.spec ib.ib p hp]
       exact ctx.sim.in_bounds p (by grind)
     case disjoint_allocs =>
       intro p₁ p₂ hp₁ hp₂ hne
       rw [TopLevelPtr.range_RegionPtr_dealloc ptr.spec ib.ib p₁ hp₁,
         TopLevelPtr.range_RegionPtr_dealloc ptr.spec ib.ib p₂ hp₂]
       exact ctx.sim.disjoint_allocs p₁ p₂ (by grind) (by grind) hne
     case encoding_op =>
       intro op hop
       have hop' : op.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_op op hop'
       have hget : op.get! (ptr.spec.dealloc ctx.spec) = op.get! ctx.spec := by grind
       have htype : op.getOpType! (ptr.spec.dealloc ctx.spec) = op.getOpType! ctx.spec := by grind [Veir.OperationPtr.getOpType!]
       have hprops : op.getProperties! (ptr.spec.dealloc ctx.spec)
           (op.getOpType! ctx.spec) = op.getProperties! ctx.spec (op.getOpType! ctx.spec) := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · have := henc.prev; grind
         · have := henc.next; grind
         · have := henc.parent; grind
         · have := henc.opType; grind
         · change ctx.buf.attributes[(Buffed.OperationMPtr.readAttrs! ctx.buf op.toM).toNat]? =
             some (op.get! (ptr.spec.dealloc ctx.spec)).attrs
           rw [hget]
           exact henc.attrs
         · rw [Erased.out_mk, htype, hprops]
           exact henc.props
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numBlockOperands
         · intro bo hbo _
           exact BlockOperandPtr.matches_RegionPtr_dealloc ptr ib fib bo hbo
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numRegions
         · intro idx hidx
           have hnum : op.getNumRegions! (ptr.spec.dealloc ctx.spec) =
               op.getNumRegions! ctx.spec := by grind
           have hreg : op.getRegion! (ptr.spec.dealloc ctx.spec) idx =
               op.getRegion! ctx.spec idx := by grind
           rw [hreg]
           exact henc.regions idx (by grind)
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numOperands
         · intro oper hoper _
           exact OpOperandPtr.matches_RegionPtr_dealloc ptr ib fib oper hoper
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numResults
         · intro res hres _
           exact OpResultPtr.matches_RegionPtr_dealloc ptr ib fib res hres
     case encoding_block =>
       intro block hblock
       have hblock' : block.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_block block hblock'
       have hget : block.get! (ptr.spec.dealloc ctx.spec) = block.get! ctx.spec := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
       · have hfib := BlockPtr.get_fieldsInBounds _ block fib hblock
         have hlay := IRContext.layoutPreserved_RegionPtr_dealloc ptr.spec ib.ib
         have htoO := BlockOperandPtr.layoutPreserved_same_toO hlay
           ((Option.maybe_def _ _ _).mp hfib.firstUse_inBounds)
         constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · have := henc.firstUse
           rw [Sim.OptionBlockOperandPtr.Sim_def] at this ⊢
           grind
         · have := henc.prev; grind
         · have := henc.next; grind
         · have := henc.parent; grind
         · have := henc.firstOp; grind
         · have := henc.lastOp; grind
       · constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
         · rw [hget]
           exact henc.numArguments
         · intro arg harg _
           exact BlockArgumentPtr.matches_RegionPtr_dealloc ptr ib fib arg harg
     case encoding_region =>
       intro region hregion
       have hregion' : region.InBounds ctx.spec := by grind
       have henc := ctx.sim.encoding_region region hregion'
       have hget : region.get! (ptr.spec.dealloc ctx.spec) = region.get! ctx.spec := by grind
       constructor <;> try simp only [Sim.RawIRContext.spec, Erased.out_mk, Erased.map_out]
       · have := henc.firstBlock; grind
       · have := henc.lastBlock; grind
       · have := henc.parent; grind
     case attr_empty => exact ctx.sim.attr_empty⟩



/-- Logically delete a detached, unreferenced block without reclaiming its bytes. -/
buffed (inline := true)
def Sim.BlockPtr.deallocSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds) : Sim.IRContext OpInfo :=
  Sim.BlockPtr.forget ctx ptr ib fib

/-- Logically delete a detached, unreferenced region without reclaiming its bytes. -/
buffed (inline := true)
def Sim.RegionPtr.deallocSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) (fib : (ptr.spec.dealloc ctx.spec).FieldsInBounds) : Sim.IRContext OpInfo :=
  Sim.RegionPtr.forget ctx ptr ib fib

end Veir
