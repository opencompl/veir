module

public meta import Veir.IR.Buffed.Meta
public import Veir.IR.Buffed.Sim
public import Veir.IR.Basic
public import Veir.IR.WellFormed
import Veir.IR.InBounds
import Veir.IR.GetSet
import Veir.IR.Buffed.Meta

import all Veir.IR.Buffed.RawAccessors
import all Veir.IR.Buffed.SimDefs
import all Veir.IR.Buffed.Sim

public section

namespace Veir


variable [HasOpInfo OpInfo]

/-! ## Debugging printers -/

@[inline]
def dumpOp (_op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpRegion (_region : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpBlock (_block : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpValue (_value : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOpResult (_result : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpBlockArgument (_arg : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOpOperand (_operand : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpBlockOperand (_operand : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

/-! ### Nullable (`Option*Ptr`) dumpers — print `null` for the sentinel. -/

@[inline]
def dumpOptionOp (_op : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionBlock (_block : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionRegion (_region : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionOpOperand (_operand : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

@[inline]
def dumpOptionBlockOperand (_operand : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) (_pref : String := "") : Sim.IRContext OpInfo := ctx

/-
@[inline]
def dumpOp (op : Sim.OperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨op.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpRegion (region : Sim.RegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨region.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpBlock (block : Sim.BlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨block.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpValue (value : Sim.ValuePtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨value.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpOpResult (result : Sim.OpResultPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨result.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpBlockArgument (arg : Sim.BlockArgumentPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨arg.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpOpOperand (operand : Sim.OpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpBlockOperand (operand : Sim.BlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

/-! ### Nullable (`Option*Ptr`) dumpers — print `null` for the sentinel. -/

@[inline]
def dumpOptionOp (op : Sim.OptionOperationPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨op.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpOptionBlock (block : Sim.OptionBlockPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨block.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpOptionRegion (region : Sim.OptionRegionPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨region.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpOptionOpOperand (operand : Sim.OptionOpOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩

@[inline]
def dumpOptionBlockOperand (operand : Sim.OptionBlockOperandPtr) (ctx : Sim.IRContext OpInfo) (pref : String := "") : Sim.IRContext OpInfo :=
  ⟨operand.impl.debugPrint pref ctx.buf, ctx.spec, sorry⟩
-/


/-! ## Setters and getters -/

buffed
def Sim.OperationPtr.setNextOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl admitted_bounds, ptr.spec.setNextOp ctx.spec next.spec (by grind), admitted_sim nextIb⟩

buffed
def Sim.OperationPtr.setNextOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl admitted_bounds, ptr.spec.setNextOp! ctx.spec next.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setNextOp_eq_setNextOp! (ctx : IRContext OpInfo) ptr next ib nextIb :
    setNextOp ctx ptr next ib nextIb = setNextOp! ctx ptr next := by
  simp [setNextOp_def, setNextOpSim, setNextOp!_def, setNextOp!Sim]
  grind

buffed
def Sim.OperationPtr.getNextOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readNext ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).next⟩

@[grind .]
theorem Sim.OperationPtr.getNextOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getNextOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).next
  grind [getNextOpSim, getNextOp_def]

@[simp, grind =]
theorem Sim.OperationPtr.getNextOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getNextOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).next := by
  rfl

buffed
def Sim.OperationPtr.getNextOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readNext! ctx.buf, (ptr.spec.get! ctx.spec).next⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNextOp_eq_getNextOp! (ctx : IRContext OpInfo) ptr ib :
    getNextOp ctx ptr ib = getNextOp! ctx ptr := by
  simp [getNextOp_def, getNextOpSim, getNextOp!_def, getNextOp!Sim]
  grind

buffed
def Sim.OperationPtr.setPrevOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl admitted_bounds, ptr.spec.setPrevOp ctx.spec prev.spec (by grind), admitted_sim prevIb⟩

buffed
def Sim.OperationPtr.setPrevOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl admitted_bounds, ptr.spec.setPrevOp! ctx.spec prev.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setPrevOp_eq_setPrevOp! (ctx : IRContext OpInfo) ptr prev ib prevIb :
    setPrevOp ctx ptr prev ib prevIb = setPrevOp! ctx ptr prev := by
  simp [setPrevOp_def, setPrevOpSim, setPrevOp!_def, setPrevOp!Sim]
  grind

@[simp, grind =]
theorem Sim.OperationPtr.setNextOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (next : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextOp ctx ptr next ib nextIb).spec = ptr.spec.setNextOp ctx.spec next.spec := by
  rfl

buffed
def Sim.OperationPtr.getPrevOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readPrev ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).prev⟩

@[simp, grind =]
theorem Sim.OperationPtr.getPrevOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).prev := by
  rfl

@[grind .]
theorem Sim.OperationPtr.getPrevOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).prev
  grind [getPrevOpSim, getPrevOp_def]

buffed
def Sim.OperationPtr.getPrevOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readPrev! ctx.buf, (ptr.spec.get! ctx.spec).prev⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getPrevOp_eq_getPrevOp! (ctx : IRContext OpInfo) ptr ib :
    getPrevOp ctx ptr ib = getPrevOp! ctx ptr := by
  simp [getPrevOp_def, getPrevOpSim, getPrevOp!_def, getPrevOp!Sim]
  grind

buffed
def Sim.OperationPtr.setParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl admitted_bounds, ptr.spec.setParent ctx.spec parent.spec (by grind), admitted_sim parentIb⟩

buffed
def Sim.OperationPtr.setParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl admitted_bounds, ptr.spec.setParent! ctx.spec parent.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent_def, setParentSim, setParent!_def, setParent!Sim]
  grind

@[simp, grind =]
theorem Sim.OperationPtr.setPrevOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (prev : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevOp ctx ptr prev ib prevIb).spec = ptr.spec.setPrevOp ctx.spec prev.spec := by
  rfl

buffed
def Sim.OperationPtr.getParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readParent ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).parent⟩

@[simp, grind =]
theorem Sim.OperationPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  rfl

@[grind .]
theorem Sim.OperationPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).parent
  grind [getParentSim, getParent_def]

buffed
def Sim.OperationPtr.getParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (ptr.spec.get! ctx.spec).parent⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent_def, getParentSim, getParent!_def, getParent!Sim]
  grind

@[simp, grind =]
theorem Sim.OperationPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (parent : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  rfl

buffed
def Sim.OperationPtr.setAttributesSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (attrs : DictionaryAttr) (_ib : ptr.InBounds ctx) : Option (Sim.IRContext OpInfo) := do
  match ctx with
  | ⟨ctxBuf, ctxSpec, ctxSim⟩ =>
    rlet ⟨ctxBuf, idx⟩ ← ctxBuf.insertAttrs attrs
    some ⟨ptr.impl.writeAttrs ctxBuf idx admitted_bounds, ptr.spec.setAttributes ctxSpec attrs admitted_bounds, admitted_sim ctxSim⟩

@[simp, grind →]
theorem Sim.OperationPtr.setAttributes_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (attrs : DictionaryAttr) (ib : ptr.InBounds ctx) :
    setAttributes ctx ptr attrs ib = some ctx →
    ctx.spec = ptr.spec.setAttributes ctx.spec attrs := by
  simp only [setAttributes_def, setAttributesSim]; grind

@[inline]
def Sim.OperationPtr.getAttributes (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) : DictionaryAttr :=
  let idx := ptr.impl.readAttrs ctx.buf admitted_bounds
  (ctx.buf.attributes[idx.toNat]'admitted_bounds).asDict admitted_bounds

@[inline]
def Sim.OperationPtr.getAttributes! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : DictionaryAttr :=
  let idx := ptr.impl.readAttrs! ctx.buf
  (ctx.buf.attributes[idx.toNat]!).asDict admitted_bounds

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getAttributes_eq_getAttributes! (ctx : IRContext OpInfo) ptr ib :
    getAttributes ctx ptr ib = getAttributes! ctx ptr := by
  simp [getAttributes, getAttributes!]
  grind

buffed
def Sim.OperationPtr.getOperandPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.OpOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeOperandOffset ctx.buf index admitted_bounds,
   ptr.spec.getOpOperand index.toNat⟩


buffed
def Sim.OperationPtr.getOperandPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.OpOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeOperandOffset! ctx.buf index,
   ptr.spec.getOpOperand index.toNat⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getOperandPtr_eq_getOperandPtr! (ctx : IRContext OpInfo) ptr index ib :
    getOperandPtr ctx ptr index ib = getOperandPtr! ctx ptr index := by
  simp [getOperandPtr_def, getOperandPtrSim, getOperandPtr!_def, getOperandPtr!Sim]

buffed
def Sim.OperationPtr.getResultPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.OpResultPtr :=
  ⟨ptr.impl + ptr.impl.computeResultOffset ctx.buf index admitted_bounds,
   ptr.spec.getResult index.toNat⟩

buffed
def Sim.OperationPtr.getResultPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.OpResultPtr :=
  ⟨ptr.impl + ptr.impl.computeResultOffset! ctx.buf index,
   ptr.spec.getResult index.toNat⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getResultPtr_eq_getResultPtr! (ctx : IRContext OpInfo) ptr index ib :
    getResultPtr ctx ptr index ib = getResultPtr! ctx ptr index := by
  simp [getResultPtr_def, getResultPtrSim, getResultPtr!_def, getResultPtr!Sim]

buffed
def Sim.OperationPtr.getRegionPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.RegionPtr :=
  ⟨ptr.impl + ptr.impl.computeRegionOffset ctx.buf index admitted_bounds,
   ptr.spec.getRegion ctx.spec index.toNat admitted_bounds admitted_bounds⟩

#print axioms Veir.OperationPtr.getRegion
#print axioms Veir.Buffed.OperationMPtr.computeRegionOffset
#print axioms Sim.OperationPtr.getRegionPtrSim

buffed
def Sim.OperationPtr.getRegionPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.RegionPtr :=
  ⟨ptr.impl + ptr.impl.computeRegionOffset! ctx.buf index,
   ptr.spec.getRegion ctx.spec index.toNat admitted_bounds admitted_bounds⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getRegionPtr_eq_getRegionPtr! (ctx : IRContext OpInfo) ptr index ib :
    getRegionPtr ctx ptr index ib = getRegionPtr! ctx ptr index := by
  simp [getRegionPtr_def, getRegionPtrSim, getRegionPtr!_def, getRegionPtr!Sim]

buffed
def Sim.OperationPtr.getBlockOperandPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.BlockOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeBlockOperandOffset ctx.buf index admitted_bounds,
   ptr.spec.getBlockOperand index.toNat⟩

buffed
def Sim.OperationPtr.getBlockOperandPtr!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr)
    (index : UInt64) : Sim.BlockOperandPtr :=
  ⟨ptr.impl + ptr.impl.computeBlockOperandOffset! ctx.buf index,
   ptr.spec.getBlockOperand index.toNat⟩

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getBlockOperandPtr_eq_getBlockOperandPtr! (ctx : IRContext OpInfo) ptr index ib :
    getBlockOperandPtr ctx ptr index ib = getBlockOperandPtr! ctx ptr index := by
  simp [getBlockOperandPtr_def, getBlockOperandPtrSim, getBlockOperandPtr!_def, getBlockOperandPtr!Sim]

@[inline]
def Sim.OperationPtr.getNumOperands (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumOperands ctx.buf admitted_bounds

@[inline]
def Sim.OperationPtr.getNumOperands! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumOperands! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumOperands_eq_getNumOperands! (ctx : IRContext OpInfo) ptr ib :
    getNumOperands ctx ptr ib = getNumOperands! ctx ptr := by
  simp [getNumOperands, getNumOperands!]

@[grind =]
theorem Sim.OperationPtr.getNumOperands!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumOperands! ctx ptr) = (ptr.spec.get! ctx.spec).capOperands.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numOperands
  simp [getNumOperands!]
  grind

@[grind =]
theorem Sim.OperationPtr.getNumOperands!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumOperands! ctx ptr) = (ptr.spec.getNumOperands! ctx.spec).toUInt64 := by
  grind [IRContext.WellFormed.operations]

@[inline]
def Sim.OperationPtr.getNumSuccessors (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumBlockOperands ctx.buf admitted_bounds

@[inline]
def Sim.OperationPtr.getNumSuccessors! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumBlockOperands! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumSuccessors_eq_getNumSuccessors! (ctx : IRContext OpInfo) ptr ib :
    getNumSuccessors ctx ptr ib = getNumSuccessors! ctx ptr := by
  simp [getNumSuccessors, getNumSuccessors!]

@[grind =]
theorem Sim.OperationPtr.getNumSuccessors!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumSuccessors! ctx ptr) = (ptr.spec.get! ctx.spec).capBlockOperands.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numBlockOperands
  simp [getNumSuccessors!]
  grind

@[grind =]
theorem Sim.OperationPtr.getNumSuccessors!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumSuccessors! ctx ptr) = (ptr.spec.getNumSuccessors! ctx.spec).toUInt64 := by
  grind [IRContext.WellFormed.operations]

@[inline]
def Sim.OperationPtr.getNumResults (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumResults ctx.buf admitted_bounds

@[inline]
def Sim.OperationPtr.getNumResults! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumResults! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumResults_eq_getNumResults! (ctx : IRContext OpInfo) ptr ib :
    getNumResults ctx ptr ib = getNumResults! ctx ptr := by
  simp [getNumResults, getNumResults!]

@[grind =]
theorem Sim.OperationPtr.getNumResults!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumResults! ctx ptr) = (ptr.spec.get! ctx.spec).capResults.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numResults
  simp [getNumResults!]
  grind

@[grind =]
theorem Sim.OperationPtr.getNumResults!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumResults! ctx ptr) = (ptr.spec.getNumResults! ctx.spec).toUInt64 := by
  grind [IRContext.WellFormed.operations]

@[inline]
def Sim.OperationPtr.getNumRegions (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumRegions ctx.buf admitted_bounds

@[inline]
def Sim.OperationPtr.getNumRegions! (ctx : Sim.IRContext OpInfo) (ptr : Sim.OperationPtr) : UInt64 :=
  ptr.impl.readNumRegions! ctx.buf

@[eq_bang, grind _=_]
theorem Sim.OperationPtr.getNumRegions_eq_getNumRegions! (ctx : IRContext OpInfo) ptr ib :
    getNumRegions ctx ptr ib = getNumRegions! ctx ptr := by
  simp [getNumRegions, getNumRegions!]

@[grind =]
theorem Sim.OperationPtr.getNumRegions!_spec (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} :
    (getNumRegions! ctx ptr) = (ptr.spec.get! ctx.spec).capRegions.toUInt64 := by
  have := (ctx.sim.encoding_op ptr.spec (by grind)).numRegions
  simp [getNumRegions!]
  grind

@[grind =]
theorem Sim.OperationPtr.getNumRegions!_spec_of_wf (ctx : IRContext OpInfo) ptr {ib : ptr.InBounds ctx} (wf : ctx.spec.WellFormed) :
    (getNumRegions! ctx ptr) = (ptr.spec.getNumRegions! ctx.spec).toUInt64 := by
  grind [IRContext.WellFormed.operations]

buffed
def Sim.OpOperandPtr.setNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl admitted_bounds, ptr.spec.setNextUse ctx.spec nextUse.spec (by grind), admitted_sim nextUseIb⟩

buffed
def Sim.OpOperandPtr.setNextUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl admitted_bounds, ptr.spec.setNextUse! ctx.spec nextUse.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setNextUse_eq_setNextUse! (ctx : IRContext OpInfo) ptr nextUse ib nextUseIb :
    setNextUse ctx ptr nextUse ib nextUseIb = setNextUse! ctx ptr nextUse := by
  simp [setNextUse_def, setNextUseSim, setNextUse!_def, setNextUse!Sim]
  grind

@[simp, grind =]
theorem Sim.OpOperandPtr.setNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (nextUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse ctx ptr nextUse ib nextUseIb).spec = ptr.spec.setNextUse ctx.spec nextUse.spec := by
  rfl

buffed
def Sim.OpOperandPtr.getNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readNextUse ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).nextUse⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).nextUse := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getNextUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.nextUse
  grind [getNextUseSim, getNextUse_def]

buffed
def Sim.OpOperandPtr.getNextUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readNextUse! ctx.buf, (ptr.spec.get! ctx.spec).nextUse⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getNextUse_eq_getNextUse! (ctx : IRContext OpInfo) ptr ib :
    getNextUse ctx ptr ib = getNextUse! ctx ptr := by
  simp [getNextUse_def, getNextUseSim, getNextUse!_def, getNextUse!Sim]
  grind

buffed
def Sim.OpOperandPtr.setBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl admitted_bounds, ptr.spec.setBack ctx.spec back.spec (by grind), admitted_sim backIb⟩

buffed
def Sim.OpOperandPtr.setBack!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl admitted_bounds, ptr.spec.setBack! ctx.spec back.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setBack_eq_setBack! (ctx : IRContext OpInfo) ptr back ib backIb :
    setBack ctx ptr back ib backIb = setBack! ctx ptr back := by
  simp [setBack_def, setBackSim, setBack!_def, setBack!Sim]
  grind

@[simp, grind =]
theorem Sim.OpOperandPtr.setBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (back : Sim.OpOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack ctx ptr back ib backIb).spec = ptr.spec.setBack ctx.spec back.spec := by
  rfl

buffed
def Sim.OpOperandPtr.getBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl.readBack ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).back⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).spec = (ptr.spec.get ctx.spec).back := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getBack_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.back
  grind [getBackSim, getBack_def]

buffed
def Sim.OpOperandPtr.getBack!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OpOperandPtrPtr :=
  ⟨ptr.impl.readBack! ctx.buf, (ptr.spec.get! ctx.spec).back⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getBack_eq_getBack! (ctx : IRContext OpInfo) ptr ib :
    getBack ctx ptr ib = getBack! ctx ptr := by
  simp [getBack_def, getBackSim, getBack!_def, getBack!Sim]
  grind

buffed
def Sim.OpOperandPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner ctx.spec owner.spec (by grind), admitted_sim ownerIb⟩

buffed
def Sim.OpOperandPtr.setOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner! ctx.spec owner.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!_def, setOwner!Sim]
  grind

@[simp, grind =]
theorem Sim.OpOperandPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

buffed
def Sim.OpOperandPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind)
    |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.OpOperandPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.OpOperandPtr.setValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl admitted_bounds, ptr.spec.setValue ctx.spec value.spec (by grind), admitted_sim valueIb⟩

buffed
def Sim.OpOperandPtr.setValue!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl admitted_bounds, ptr.spec.setValue! ctx.spec value.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.setValue_eq_setValue! (ctx : IRContext OpInfo) ptr value ib valueIb :
    setValue ctx ptr value ib valueIb = setValue! ctx ptr value := by
  simp [setValue_def, setValueSim, setValue!_def, setValue!Sim]
  grind

@[simp, grind =]
theorem Sim.OpOperandPtr.setValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (value : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue ctx ptr value ib valueIb).spec = ptr.spec.setValue ctx.spec value.spec := by
  rfl

buffed
def Sim.OpOperandPtr.getValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.ValuePtr :=
  ⟨ptr.impl.readValue ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).value⟩

@[simp, grind =]
theorem Sim.OpOperandPtr.getValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).spec = (ptr.spec.get ctx.spec).value := by
  rfl

@[grind .]
theorem Sim.OpOperandPtr.getValue_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpOperandPtr.inBounds_def])
    |>.operands ptr.spec (by grind) (by grind) |>.value
  grind [getValueSim, getValue_def]

buffed
def Sim.OpOperandPtr.getValue!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtr) : Sim.ValuePtr :=
  ⟨ptr.impl.readValue! ctx.buf, (ptr.spec.get! ctx.spec).value⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtr.getValue_eq_getValue! (ctx : IRContext OpInfo) ptr ib :
    getValue ctx ptr ib = getValue! ctx ptr := by
  simp [getValue_def, getValueSim, getValue!_def, getValue!Sim]
  grind

buffed
def Sim.OpResultPtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), admitted_sim firstUseIb⟩

buffed
def Sim.OpResultPtr.setFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse! ctx.spec firstUse.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!_def, setFirstUse!Sim]
  grind

@[simp, grind =]
theorem Sim.OpResultPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

buffed
def Sim.OpResultPtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).firstUse⟩

@[simp, grind =]
theorem Sim.OpResultPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  rfl

@[grind .]
theorem Sim.OpResultPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpResultPtr.inBounds_def])
    |>.results ptr.spec (by grind) (by grind) |>.firstUse
  grind [getFirstUseSim, getFirstUse_def]

buffed
def Sim.OpResultPtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (ptr.spec.get! ctx.spec).firstUse⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.OpResultPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner ctx.spec owner.spec (by grind), admitted_sim ownerIb⟩

buffed
def Sim.OpResultPtr.setOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner! ctx.spec owner.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!_def, setOwner!Sim]
  grind

@[simp, grind =]
theorem Sim.OpResultPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

buffed
def Sim.OpResultPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.OpResultPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.OpResultPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.OpResultPtr.inBounds_def])
    |>.results ptr.spec (by grind) (by grind) |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.OpResultPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpResultPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.OpResultPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.BlockArgumentPtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), admitted_sim firstUseIb⟩

buffed
def Sim.BlockArgumentPtr.setFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse! ctx.spec firstUse.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!_def, setFirstUse!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

buffed
def Sim.BlockArgumentPtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).firstUse⟩

@[simp, grind =]
theorem Sim.BlockArgumentPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  rfl

@[grind .]
theorem Sim.BlockArgumentPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_block ptr.spec.block (by grind [Veir.BlockArgumentPtr.inBounds_def])
   |>.arguments ptr.spec (by grind) (by grind) |>.firstUse
  grind [getFirstUseSim, getFirstUse_def]

buffed
def Sim.BlockArgumentPtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (ptr.spec.get! ctx.spec).firstUse⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.BlockArgumentPtr.setIndexSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : Nat)
    (ib : ptr.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeIndex ctx.buf index.toUInt64 admitted_bounds, ptr.spec.setIndex ctx.spec index (by grind), admitted_sim ib⟩

buffed
def Sim.BlockArgumentPtr.setIndex!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : Nat) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeIndex ctx.buf index.toUInt64 admitted_bounds, ptr.spec.setIndex! ctx.spec index, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setIndex_eq_setIndex! (ctx : IRContext OpInfo) ptr index ib :
    setIndex ctx ptr index ib = setIndex! ctx ptr index := by
  simp [setIndex_def, setIndexSim, setIndex!_def, setIndex!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setIndex_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (index : Nat)
    (ib : ptr.InBounds ctx) :
    (setIndex ctx ptr index ib).spec = ptr.spec.setIndex ctx.spec index := by
  rfl

@[inline]
def Sim.BlockArgumentPtr.getIndexSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
  (_index : Nat)
    (ib : ptr.InBounds ctx) : Nat :=
  (ptr.spec.get ctx.spec).index

@[inline]
def Sim.BlockArgumentPtr.getIndex!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (_index : Nat) : Nat :=
  (ptr.spec.get! ctx.spec).index

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getIndex_eq_getIndex! (ctx : IRContext OpInfo) ptr index ib :
    getIndexSim ctx ptr index ib = getIndex!Sim ctx ptr index := by
  simp [getIndexSim, getIndex!Sim]
  grind

buffed
def Sim.BlockArgumentPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner ctx.spec owner.spec (by grind), admitted_sim ownerIb⟩

buffed
def Sim.BlockArgumentPtr.setOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner! ctx.spec owner.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!_def, setOwner!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockArgumentPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (owner : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

buffed
def Sim.BlockArgumentPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockPtr :=
  ⟨ptr.impl.readOwner ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.BlockArgumentPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.BlockArgumentPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_block ptr.spec.block (by simp; grind [Veir.BlockArgumentPtr.inBounds_def])
    |>.arguments ptr.spec (by grind) (by grind) |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.BlockArgumentPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockArgumentPtr) : Sim.BlockPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.BlockArgumentPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl admitted_bounds, ptr.spec.setNextUse ctx.spec nextUse.spec (by grind), admitted_sim nextUseIb⟩

buffed
def Sim.BlockOperandPtr.setNextUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNextUse ctx.buf nextUse.impl admitted_bounds, ptr.spec.setNextUse! ctx.spec nextUse.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setNextUse_eq_setNextUse! (ctx : IRContext OpInfo) ptr nextUse ib nextUseIb :
    setNextUse ctx ptr nextUse ib nextUseIb = setNextUse! ctx ptr nextUse := by
  simp [setNextUse_def, setNextUseSim, setNextUse!_def, setNextUse!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockOperandPtr.setNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (nextUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (nextUseIb : nextUse.InBounds ctx) :
    (setNextUse ctx ptr nextUse ib nextUseIb).spec = ptr.spec.setNextUse ctx.spec nextUse.spec := by
  rfl

buffed
def Sim.BlockOperandPtr.getNextUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readNextUse ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).nextUse⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getNextUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).nextUse := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getNextUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getNextUse ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.nextUse
  grind [getNextUseSim, getNextUse_def]

buffed
def Sim.BlockOperandPtr.getNextUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readNextUse! ctx.buf, (ptr.spec.get! ctx.spec).nextUse⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getNextUse_eq_getNextUse! (ctx : IRContext OpInfo) ptr ib :
    getNextUse ctx ptr ib = getNextUse! ctx ptr := by
  simp [getNextUse_def, getNextUseSim, getNextUse!_def, getNextUse!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl admitted_bounds, ptr.spec.setBack ctx.spec back.spec (by grind), admitted_sim backIb⟩

buffed
def Sim.BlockOperandPtr.setBack!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeBack ctx.buf back.impl admitted_bounds, ptr.spec.setBack! ctx.spec back.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setBack_eq_setBack! (ctx : IRContext OpInfo) ptr back ib backIb :
    setBack ctx ptr back ib backIb = setBack! ctx ptr back := by
  simp [setBack_def, setBackSim, setBack!_def, setBack!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockOperandPtr.setBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (back : Sim.BlockOperandPtrPtr)
    (ib : ptr.InBounds ctx) (backIb : back.InBounds ctx) :
    (setBack ctx ptr back ib backIb).spec = ptr.spec.setBack ctx.spec back.spec := by
  rfl

buffed
def Sim.BlockOperandPtr.getBackSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl.readBack ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).back⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getBack_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).spec = (ptr.spec.get ctx.spec).back := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getBack_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getBack ctx ptr ib).Sim ctx.inner := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.back
  grind [getBackSim, getBack_def]

buffed
def Sim.BlockOperandPtr.getBack!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.BlockOperandPtrPtr :=
  ⟨ptr.impl.readBack! ctx.buf, (ptr.spec.get! ctx.spec).back⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getBack_eq_getBack! (ctx : IRContext OpInfo) ptr ib :
    getBack ctx ptr ib = getBack! ctx ptr := by
  simp [getBack_def, getBackSim, getBack!_def, getBack!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner ctx.spec owner.spec (by grind), admitted_sim ownerIb⟩

buffed
def Sim.BlockOperandPtr.setOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeOwner ctx.buf owner.impl admitted_bounds, ptr.spec.setOwner! ctx.spec owner.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setOwner_eq_setOwner! (ctx : IRContext OpInfo) ptr owner ib ownerIb :
    setOwner ctx ptr owner ib ownerIb = setOwner! ctx ptr owner := by
  simp [setOwner_def, setOwnerSim, setOwner!_def, setOwner!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockOperandPtr.setOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (owner : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (ownerIb : owner.InBounds ctx) :
    (setOwner ctx ptr owner ib ownerIb).spec = ptr.spec.setOwner ctx.spec owner.spec := by
  rfl

buffed
def Sim.BlockOperandPtr.getOwnerSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).owner⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getOwner_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).spec = (ptr.spec.get ctx.spec).owner := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getOwner_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getOwner ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.owner
  grind [getOwnerSim, getOwner_def]

buffed
def Sim.BlockOperandPtr.getOwner!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.OperationPtr :=
  ⟨ptr.impl.readOwner! ctx.buf, (ptr.spec.get! ctx.spec).owner⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getOwner_eq_getOwner! (ctx : IRContext OpInfo) ptr ib :
    getOwner ctx ptr ib = getOwner! ctx ptr := by
  simp [getOwner_def, getOwnerSim, getOwner!_def, getOwner!Sim]
  grind

buffed
def Sim.BlockOperandPtr.setValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl admitted_bounds, ptr.spec.setValue ctx.spec value.spec (by grind), admitted_sim valueIb⟩

buffed
def Sim.BlockOperandPtr.setValue!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeValue ctx.buf value.impl admitted_bounds, ptr.spec.setValue! ctx.spec value.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.setValue_eq_setValue! (ctx : IRContext OpInfo) ptr value ib valueIb :
    setValue ctx ptr value ib valueIb = setValue! ctx ptr value := by
  simp [setValue_def, setValueSim, setValue!_def, setValue!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockOperandPtr.setValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (value : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (setValue ctx ptr value ib valueIb).spec = ptr.spec.setValue ctx.spec value.spec := by
  rfl

buffed
def Sim.BlockOperandPtr.getValueSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) : Sim.BlockPtr :=
  ⟨ptr.impl.readValue ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).value⟩

@[simp, grind =]
theorem Sim.BlockOperandPtr.getValue_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).spec = (ptr.spec.get ctx.spec).value := by
  rfl

@[grind .]
theorem Sim.BlockOperandPtr.getValue_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr)
    (ib : ptr.InBounds ctx) :
    (getValue ctx ptr ib).Sim := by
  have := ctx.sim.encoding_op ptr.spec.op (by grind [Veir.BlockOperandPtr.inBounds_def])
    |>.blockOperands ptr.spec (by grind) (by grind) |>.value
  grind [getValueSim, getValue_def]

buffed
def Sim.BlockOperandPtr.getValue!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtr) : Sim.BlockPtr :=
  ⟨ptr.impl.readValue! ctx.buf, (ptr.spec.get! ctx.spec).value⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtr.getValue_eq_getValue! (ctx : IRContext OpInfo) ptr ib :
    getValue ctx ptr ib = getValue! ctx ptr := by
  simp [getValue_def, getValueSim, getValue!_def, getValue!Sim]
  grind

@[inline]
def Sim.BlockPtr.allocEmptyImpl (ctx : Buffed.IRBufContext OpInfo) (numArgs : UInt64) : Option (Buffed.IRBufContext OpInfo × Buffed.BlockMPtr) := do
  let size := Buffed.BlockMPtr.computeBlockSize numArgs
  let ptr : Buffed.BlockMPtr := ctx.usize
  let ctx ← ctx.alloc size.toUInt64
  let ctx := ptr.writeNumArguments ctx numArgs admitted_bounds
  let ctx := ptr.writeFirstUse ctx .none admitted_bounds
  let ctx := ptr.writePrev ctx .none admitted_bounds
  let ctx := ptr.writeNext ctx .none admitted_bounds
  let ctx := ptr.writeParent ctx .none admitted_bounds
  let ctx := ptr.writeFirstOp ctx .none admitted_bounds
  let ctx := ptr.writeLastOp ctx .none admitted_bounds
  some (ctx, ptr)

@[noinline]
def Sim.BlockPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (capArguments : Nat) (address : UInt64) : Option (Veir.IRContext OpInfo × Veir.BlockPtr) :=
  BlockPtr.allocEmptyAtAddress ctx address.toNat capArguments

@[inline]
def Sim.BlockPtr.allocEmpty (ctx : Sim.IRContext OpInfo) (numArgs : UInt64) : Option (Sim.BlockPtr × Sim.IRContext OpInfo) :=
  match allocEmptyImpl ctx.buf numArgs with
  | none => none
  | some (ctxBuf, ptrImpl) =>
    let ⟨ctxSpec, ptrSpec⟩ := (allocEmptySpec ctx.spec numArgs.toNat ptrImpl).specGet!
    some ⟨⟨ptrImpl, ptrSpec⟩, ⟨ctxBuf, ctxSpec, admitted_sim ()⟩⟩

@[grind! .]
theorem Sim.BlockPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} numArgs :
    allocEmpty ctx numArgs = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.BlockPtr.allocEmptyAtAddress ctx.spec numArgs.toNat addr = some ⟨ctx'.spec, ptr.spec⟩:= by
  sorry

buffed
def Sim.BlockPtr.setParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl admitted_bounds, ptr.spec.setParent ctx.spec parent.spec (by grind), admitted_sim parentIb⟩

buffed
def Sim.BlockPtr.setParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl admitted_bounds, ptr.spec.setParent! ctx.spec parent.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent_def, setParentSim, setParent!_def, setParent!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (parent : Sim.OptionRegionPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  rfl

buffed
def Sim.BlockPtr.getParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionRegionPtr :=
  ⟨ptr.impl.readParent ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).parent⟩

@[simp, grind =]
theorem Sim.BlockPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).parent
  grind [getParentSim, getParent_def]

buffed
def Sim.BlockPtr.getParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionRegionPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (ptr.spec.get! ctx.spec).parent⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent_def, getParentSim, getParent!_def, getParent!Sim]
  grind

buffed
def Sim.BlockPtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), admitted_sim firstUseIb⟩

buffed
def Sim.BlockPtr.setFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse! ctx.spec firstUse.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!_def, setFirstUse!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockPtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstUse : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

buffed
def Sim.BlockPtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).firstUse⟩

@[simp, grind =]
theorem Sim.BlockPtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstUse := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).firstUse
  grind [getFirstUseSim, getFirstUse_def]

buffed
def Sim.BlockPtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, (ptr.spec.get! ctx.spec).firstUse⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.BlockPtr.setFirstOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstOp ctx.buf firstOp.impl admitted_bounds, ptr.spec.setFirstOp ctx.spec firstOp.spec (by grind), admitted_sim firstOpIb⟩

buffed
def Sim.BlockPtr.setFirstOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstOp ctx.buf firstOp.impl admitted_bounds, ptr.spec.setFirstOp! ctx.spec firstOp.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setFirstOp_eq_setFirstOp! (ctx : IRContext OpInfo) ptr firstOp ib firstOpIb :
    setFirstOp ctx ptr firstOp ib firstOpIb = setFirstOp! ctx ptr firstOp := by
  simp [setFirstOp_def, setFirstOpSim, setFirstOp!_def, setFirstOp!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockPtr.setFirstOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (firstOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (firstOpIb : firstOp.InBounds ctx) :
    (setFirstOp ctx ptr firstOp ib firstOpIb).spec = ptr.spec.setFirstOp ctx.spec firstOp.spec := by
  rfl

buffed
def Sim.BlockPtr.getFirstOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readFirstOp ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).firstOp⟩

@[simp, grind =]
theorem Sim.BlockPtr.getFirstOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstOp := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getFirstOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).firstOp
  grind [getFirstOpSim, getFirstOp_def]

buffed
def Sim.BlockPtr.getFirstOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readFirstOp! ctx.buf, (ptr.spec.get! ctx.spec).firstOp⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getFirstOp_eq_getFirstOp! (ctx : IRContext OpInfo) ptr ib :
    getFirstOp ctx ptr ib = getFirstOp! ctx ptr := by
  simp [getFirstOp_def, getFirstOpSim, getFirstOp!_def, getFirstOp!Sim]
  grind

buffed
def Sim.BlockPtr.setLastOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastOp ctx.buf lastOp.impl admitted_bounds, ptr.spec.setLastOp ctx.spec lastOp.spec (by grind), admitted_sim lastOpIb⟩

buffed
def Sim.BlockPtr.setLastOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastOp ctx.buf lastOp.impl admitted_bounds, ptr.spec.setLastOp! ctx.spec lastOp.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setLastOp_eq_setLastOp! (ctx : IRContext OpInfo) ptr lastOp ib lastOpIb :
    setLastOp ctx ptr lastOp ib lastOpIb = setLastOp! ctx ptr lastOp := by
  simp [setLastOp_def, setLastOpSim, setLastOp!_def, setLastOp!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockPtr.setLastOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (lastOp : Sim.OptionOperationPtr)
    (ib : ptr.InBounds ctx) (lastOpIb : lastOp.InBounds ctx) :
    (setLastOp ctx ptr lastOp ib lastOpIb).spec = ptr.spec.setLastOp ctx.spec lastOp.spec := by
  rfl

buffed
def Sim.BlockPtr.getLastOpSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readLastOp ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).lastOp⟩

@[simp, grind =]
theorem Sim.BlockPtr.getLastOp_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getLastOp ctx ptr ib).spec = (ptr.spec.get ctx.spec).lastOp := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getLastOp_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getLastOp ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).lastOp
  grind [getLastOpSim, getLastOp_def]

buffed
def Sim.BlockPtr.getLastOp!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readLastOp! ctx.buf, (ptr.spec.get! ctx.spec).lastOp⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getLastOp_eq_getLastOp! (ctx : IRContext OpInfo) ptr ib :
    getLastOp ctx ptr ib = getLastOp! ctx ptr := by
  simp [getLastOp_def, getLastOpSim, getLastOp!_def, getLastOp!Sim]
  grind

buffed
def Sim.BlockPtr.setNextBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl admitted_bounds, ptr.spec.setNextBlock ctx.spec next.spec (by grind), admitted_sim nextIb⟩

buffed
def Sim.BlockPtr.setNextBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeNext ctx.buf next.impl admitted_bounds, ptr.spec.setNextBlock! ctx.spec next.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setNextBlock_eq_setNextBlock! (ctx : IRContext OpInfo) ptr next ib nextIb :
    setNextBlock ctx ptr next ib nextIb = setNextBlock! ctx ptr next := by
  simp [setNextBlock_def, setNextBlockSim, setNextBlock!_def, setNextBlock!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockPtr.setNextBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (next : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (nextIb : next.InBounds ctx) :
    (setNextBlock ctx ptr next ib nextIb).spec = ptr.spec.setNextBlock ctx.spec next.spec := by
  rfl

buffed
def Sim.BlockPtr.getNextBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readNext ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).next⟩

@[simp, grind =]
theorem Sim.BlockPtr.getNextBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNextBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).next := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getNextBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNextBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).next
  grind [getNextBlockSim, getNextBlock_def]

buffed
def Sim.BlockPtr.getNextBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readNext! ctx.buf, (ptr.spec.get! ctx.spec).next⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getNextBlock_eq_getNextBlock! (ctx : IRContext OpInfo) ptr ib :
    getNextBlock ctx ptr ib = getNextBlock! ctx ptr := by
  simp [getNextBlock_def, getNextBlockSim, getNextBlock!_def, getNextBlock!Sim]
  grind

buffed
def Sim.BlockPtr.setPrevBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl admitted_bounds, ptr.spec.setPrevBlock ctx.spec prev.spec (by grind), admitted_sim prevIb⟩

buffed
def Sim.BlockPtr.setPrevBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writePrev ctx.buf prev.impl admitted_bounds, ptr.spec.setPrevBlock! ctx.spec prev.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.setPrevBlock_eq_setPrevBlock! (ctx : IRContext OpInfo) ptr prev ib prevIb :
    setPrevBlock ctx ptr prev ib prevIb = setPrevBlock! ctx ptr prev := by
  simp [setPrevBlock_def, setPrevBlockSim, setPrevBlock!_def, setPrevBlock!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockPtr.setPrevBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (prev : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (prevIb : prev.InBounds ctx) :
    (setPrevBlock ctx ptr prev ib prevIb).spec = ptr.spec.setPrevBlock ctx.spec prev.spec := by
  rfl

buffed
def Sim.BlockPtr.getPrevBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readPrev ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).prev⟩

@[simp, grind =]
theorem Sim.BlockPtr.getPrevBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).prev := by
  rfl

@[grind .]
theorem Sim.BlockPtr.getPrevBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getPrevBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).prev
  grind [getPrevBlockSim, getPrevBlock_def]

buffed
def Sim.BlockPtr.getPrevBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readPrev! ctx.buf, (ptr.spec.get! ctx.spec).prev⟩

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getPrevBlock_eq_getPrevBlock! (ctx : IRContext OpInfo) ptr ib :
    getPrevBlock ctx ptr ib = getPrevBlock! ctx ptr := by
  simp [getPrevBlock_def, getPrevBlockSim, getPrevBlock!_def, getPrevBlock!Sim]
  grind

@[inline]
def Sim.BlockPtr.getNumArguments (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (_ib : ptr.InBounds ctx) : UInt64 :=
  ptr.impl.readNumArguments ctx.buf admitted_bounds

@[inline]
def Sim.BlockPtr.getNumArguments! (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr) : UInt64 :=
  ptr.impl.readNumArguments! ctx.buf

@[simp, grind =]
theorem Sim.BlockPtr.getNumArguments_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (ib : ptr.InBounds ctx) :
    (getNumArguments ctx ptr ib).toNat = (ptr.spec.get! ctx.spec).capArguments := by
  have := (ctx.sim.encoding_block ptr.spec (by grind)).numArguments
  grind [getNumArguments]

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getNumArguments_eq_getNumArguments! (ctx : IRContext OpInfo) ptr ib :
    getNumArguments ctx ptr ib = getNumArguments! ctx ptr := by
  simp [getNumArguments, getNumArguments!]

buffed
def Sim.BlockPtr.getArgumentPtrSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) (_ib : ptr.InBounds ctx) : Sim.BlockArgumentPtr :=
  ⟨ptr.impl + ptr.impl.computeArgumentOffset ctx.buf index admitted_bounds,
   ptr.spec.getArgument index.toNat⟩

buffed
def Sim.BlockPtr.getArgumentPtr!Sim (_ctx : IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) : Sim.BlockArgumentPtr :=
  ⟨ptr.impl + Buffed.BlockMPtr.computeArgumentOffset! index,
   ptr.spec.getArgument index.toNat⟩

@[simp, grind =]
theorem Sim.BlockPtr.getArgumentPtr_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockPtr)
    (index : UInt64) (ib : ptr.InBounds ctx) :
    (getArgumentPtr ctx ptr index ib).spec = ptr.spec.getArgument index.toNat := by
  rfl

@[eq_bang, grind _=_]
theorem Sim.BlockPtr.getArgumentPtr_eq_getArgumentPtr! (ctx : IRContext OpInfo) ptr index ib :
    getArgumentPtr ctx ptr index ib = getArgumentPtr! ctx ptr index := by
  simp [getArgumentPtr_def, getArgumentPtrSim, getArgumentPtr!_def, getArgumentPtr!Sim]

buffed
def Sim.RegionPtr.setParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl admitted_bounds, ptr.spec.setParent ctx.spec parent.spec (by grind), admitted_sim parentIb⟩

buffed
def Sim.RegionPtr.setParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OperationPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeParent ctx.buf parent.impl admitted_bounds, ptr.spec.setParent! ctx.spec parent.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setParent_eq_setParent! (ctx : IRContext OpInfo) ptr parent ib parentIb :
    setParent ctx ptr parent ib parentIb = setParent! ctx ptr parent := by
  simp [setParent_def, setParentSim, setParent!_def, setParent!Sim]
  grind

@[simp, grind =]
theorem Sim.RegionPtr.setParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (parent : Sim.OperationPtr)
    (ib : ptr.InBounds ctx) (parentIb : parent.InBounds ctx) :
    (setParent ctx ptr parent ib parentIb).spec = ptr.spec.setParent ctx.spec parent.spec := by
  rfl

buffed
def Sim.RegionPtr.getParentSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readParent ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).parent⟩

@[simp, grind =]
theorem Sim.RegionPtr.getParent_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).spec = (ptr.spec.get ctx.spec).parent := by
  rfl

@[grind .]
theorem Sim.RegionPtr.getParent_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) (ib : ptr.InBounds ctx) :
    (getParent ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).parent
  grind [getParentSim, getParent_def]

buffed
def Sim.RegionPtr.getParent!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionOperationPtr :=
  ⟨ptr.impl.readParent! ctx.buf, (ptr.spec.get! ctx.spec).parent⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getParent_eq_getParent! (ctx : IRContext OpInfo) ptr ib :
    getParent ctx ptr ib = getParent! ctx ptr := by
  simp [getParent_def, getParentSim, getParent!_def, getParent!Sim]
  grind

buffed
def Sim.RegionPtr.setFirstBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstBlock ctx.buf firstBlock.impl admitted_bounds, ptr.spec.setFirstBlock ctx.spec firstBlock.spec (by grind), admitted_sim firstBlockIb⟩

buffed
def Sim.RegionPtr.setFirstBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstBlock ctx.buf firstBlock.impl admitted_bounds, ptr.spec.setFirstBlock! ctx.spec firstBlock.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setFirstBlock_eq_setFirstBlock! (ctx : IRContext OpInfo) ptr firstBlock ib firstBlockIb :
    setFirstBlock ctx ptr firstBlock ib firstBlockIb = setFirstBlock! ctx ptr firstBlock := by
  simp [setFirstBlock_def, setFirstBlockSim, setFirstBlock!_def, setFirstBlock!Sim]
  grind

@[simp, grind =]
theorem Sim.RegionPtr.setFirstBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (firstBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (firstBlockIb : firstBlock.InBounds ctx) :
    (setFirstBlock ctx ptr firstBlock ib firstBlockIb).spec = ptr.spec.setFirstBlock ctx.spec firstBlock.spec := by
  rfl

buffed
def Sim.RegionPtr.getFirstBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readFirstBlock ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).firstBlock⟩

@[simp, grind =]
theorem Sim.RegionPtr.getFirstBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).firstBlock := by
  rfl

@[grind .]
theorem Sim.RegionPtr.getFirstBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getFirstBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).firstBlock
  grind [getFirstBlockSim, getFirstBlock_def]

buffed
def Sim.RegionPtr.getFirstBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readFirstBlock! ctx.buf, (ptr.spec.get! ctx.spec).firstBlock⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getFirstBlock_eq_getFirstBlock! (ctx : IRContext OpInfo) ptr ib :
    getFirstBlock ctx ptr ib = getFirstBlock! ctx ptr := by
  simp [getFirstBlock_def, getFirstBlockSim, getFirstBlock!_def, getFirstBlock!Sim]
  grind

buffed
def Sim.RegionPtr.setLastBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastBlock ctx.buf lastBlock.impl admitted_bounds, ptr.spec.setLastBlock ctx.spec lastBlock.spec (by grind), admitted_sim lastBlockIb⟩

buffed
def Sim.RegionPtr.setLastBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeLastBlock ctx.buf lastBlock.impl admitted_bounds, ptr.spec.setLastBlock! ctx.spec lastBlock.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.setLastBlock_eq_setLastBlock! (ctx : IRContext OpInfo) ptr lastBlock ib lastBlockIb :
    setLastBlock ctx ptr lastBlock ib lastBlockIb = setLastBlock! ctx ptr lastBlock := by
  simp [setLastBlock_def, setLastBlockSim, setLastBlock!_def, setLastBlock!Sim]
  grind

@[simp, grind =]
theorem Sim.RegionPtr.setLastBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (lastBlock : Sim.OptionBlockPtr)
    (ib : ptr.InBounds ctx) (lastBlockIb : lastBlock.InBounds ctx) :
    (setLastBlock ctx ptr lastBlock ib lastBlockIb).spec = ptr.spec.setLastBlock ctx.spec lastBlock.spec := by
  rfl

buffed
def Sim.RegionPtr.getLastBlockSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readLastBlock ctx.buf admitted_bounds, (ptr.spec.get ctx.spec).lastBlock⟩

@[simp, grind =]
theorem Sim.RegionPtr.getLastBlock_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getLastBlock ctx ptr ib).spec = (ptr.spec.get ctx.spec).lastBlock := by
  rfl

@[grind .]
theorem Sim.RegionPtr.getLastBlock_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr)
    (ib : ptr.InBounds ctx) :
    (getLastBlock ctx ptr ib).Sim := by
  have := (ctx.sim.encoding_region ptr.spec (by grind)).lastBlock
  grind [getLastBlockSim, getLastBlock_def]

buffed
def Sim.RegionPtr.getLastBlock!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.RegionPtr) : Sim.OptionBlockPtr :=
  ⟨ptr.impl.readLastBlock! ctx.buf, (ptr.spec.get! ctx.spec).lastBlock⟩

@[eq_bang, grind _=_]
theorem Sim.RegionPtr.getLastBlock_eq_getLastBlock! (ctx : IRContext OpInfo) ptr ib :
    getLastBlock ctx ptr ib = getLastBlock! ctx ptr := by
  simp [getLastBlock_def, getLastBlockSim, getLastBlock!_def, getLastBlock!Sim]
  grind

buffed
def Sim.ValuePtr.setFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse ctx.spec firstUse.spec (by grind), admitted_sim firstUseIb⟩

buffed
def Sim.ValuePtr.setFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.writeFirstUse ctx.buf firstUse.impl admitted_bounds, ptr.spec.setFirstUse! ctx.spec firstUse.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.ValuePtr.setFirstUse_eq_setFirstUse! (ctx : IRContext OpInfo) ptr firstUse ib firstUseIb :
    setFirstUse ctx ptr firstUse ib firstUseIb = setFirstUse! ctx ptr firstUse := by
  simp [setFirstUse_def, setFirstUseSim, setFirstUse!_def, setFirstUse!Sim]
  grind

@[simp, grind =]
theorem Sim.ValuePtr.setFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (firstUse : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (firstUseIb : firstUse.InBounds ctx) :
    (setFirstUse ctx ptr firstUse ib firstUseIb).spec = ptr.spec.setFirstUse ctx.spec firstUse.spec := by
  rfl

buffed
def Sim.ValuePtr.getFirstUseSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse ctx.buf admitted_bounds, ptr.spec.getFirstUse ctx.spec (by grind)⟩

@[simp, grind =]
theorem Sim.ValuePtr.getFirstUse_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).spec = ptr.spec.getFirstUse ctx.spec (by grind) := by
  rfl

@[grind .]
theorem Sim.ValuePtr.getFirstUse_sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr)
    (ib : ptr.InBounds ctx) :
    (getFirstUse ctx ptr ib).Sim ctx.inner := by
  cases heq : ptr.spec
  case opResult res =>
    have := ctx.sim.encoding_op res.op (by grind [Veir.OpResultPtr.inBounds_def])
      |>.results res (by grind) (by grind) |>.firstUse
    simp_all [getFirstUseSim, getFirstUse_def, eq_bang]
    unfold Buffed.OpResultMPtr.readFirstUse! at this
    unfold Buffed.ValueImplMPtr.readFirstUse!
    grind
  case blockArgument arg =>
    have := ctx.sim.encoding_block arg.block (by grind [Veir.BlockArgumentPtr.inBounds_def])
      |>.arguments arg (by grind) (by grind) |>.firstUse
    simp_all [getFirstUseSim, getFirstUse_def, eq_bang]
    unfold Buffed.BlockArgumentMPtr.readFirstUse! at this
    unfold Buffed.ValueImplMPtr.readFirstUse!
    grind

buffed
def Sim.ValuePtr.getFirstUse!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.ValuePtr) : Sim.OptionOpOperandPtr :=
  ⟨ptr.impl.readFirstUse! ctx.buf, ptr.spec.getFirstUse! ctx.spec⟩

@[eq_bang, grind _=_]
theorem Sim.ValuePtr.getFirstUse_eq_getFirstUse! (ctx : IRContext OpInfo) ptr ib :
    getFirstUse ctx ptr ib = getFirstUse! ctx ptr := by
  simp [getFirstUse_def, getFirstUseSim, getFirstUse!_def, getFirstUse!Sim]
  grind

buffed
def Sim.OpOperandPtrPtr.setSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl admitted_bounds, ptr.spec.set ctx.spec value.spec (by grind), admitted_sim valueIb⟩

buffed
def Sim.OpOperandPtrPtr.set!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl admitted_bounds, ptr.spec.set! ctx.spec value.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.OpOperandPtrPtr.set_eq_set! (ctx : IRContext OpInfo) ptr value ib valueIb :
    set ctx ptr value ib valueIb = set! ctx ptr value := by
  simp [set_def, setSim, set!_def, set!Sim]
  grind

@[simp, grind =]
theorem Sim.OpOperandPtrPtr.setSim_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.OpOperandPtrPtr)
    (value : Sim.OptionOpOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (set ctx ptr value ib valueIb).spec = ptr.spec.set ctx.spec value.spec := by
  rfl

buffed
def Sim.BlockOperandPtrPtr.setSim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl admitted_bounds, ptr.spec.set ctx.spec value.spec (by grind), admitted_sim valueIb⟩

buffed
def Sim.BlockOperandPtrPtr.set!Sim (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr) : Sim.IRContext OpInfo :=
  ⟨ptr.impl.write ctx.buf value.impl admitted_bounds, ptr.spec.set! ctx.spec value.spec, admitted_sim ()⟩

@[eq_bang, grind _=_]
theorem Sim.BlockOperandPtrPtr.set_eq_set! (ctx : IRContext OpInfo) ptr value ib valueIb :
    set ctx ptr value ib valueIb = set! ctx ptr value := by
  simp [set_def, setSim, set!_def, set!Sim]
  grind

@[simp, grind =]
theorem Sim.BlockOperandPtrPtr.setSim_spec (ctx : Sim.IRContext OpInfo) (ptr : Sim.BlockOperandPtrPtr)
    (value : Sim.OptionBlockOperandPtr)
    (ib : ptr.InBounds ctx) (valueIb : value.InBounds ctx) :
    (set ctx ptr value ib valueIb).spec = ptr.spec.set ctx.spec value.spec := by
  rfl

/-! ## Allocation of empty regions and operations.

Like `Sim.BlockPtr.allocEmpty`, these reserve buffer space (with preallocated arrays for the
operation) and allocate the corresponding pointer in the specification. -/

@[inline]
def Sim.RegionPtr.allocEmptyImpl (ctx : Buffed.IRBufContext OpInfo) : Option (Buffed.IRBufContext OpInfo × Buffed.RegionMPtr) := do
  let size := Buffed.Region.size
  let ptr : Buffed.RegionMPtr := ctx.usize
  let ctx ← ctx.alloc size
  let ctx := ptr.writeParent ctx .none admitted_bounds
  let ctx := ptr.writeFirstBlock ctx .none admitted_bounds
  let ctx := ptr.writeLastBlock ctx .none admitted_bounds
  some (ctx, ptr)

def Sim.RegionPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (addr : UInt64) : Option (Veir.IRContext OpInfo × Veir.RegionPtr) :=
  RegionPtr.allocEmptyAt ctx addr.toNat

@[inline]
def Sim.RegionPtr.allocEmpty (ctx : Sim.IRContext OpInfo) : Option (Sim.RegionPtr × Sim.IRContext OpInfo) := do
  match allocEmptyImpl ctx.buf with
  | none => none
  | some (ctxBuf, ptrImpl) =>
    let ⟨ctxSpec, ptrSpec⟩ := (allocEmptySpec ctx.spec ptrImpl).specGet!
    some ⟨⟨ptrImpl, ptrSpec⟩, ⟨ctxBuf, ctxSpec, admitted_sim ()⟩⟩

@[inline]
def Sim.OperationPtr.allocEmptyImpl (ctx : Buffed.IRBufContext OpInfo)
    (numResults numOperands numBlockOperands numRegions propSize : UInt64) :
    Option (Buffed.IRBufContext OpInfo × Buffed.OperationMPtr) := do
  let size := Buffed.OperationMPtr.computeOperationSize numResults numOperands numBlockOperands numRegions propSize
  -- The operation pointer points past the (back-allocated) results array.
  let ptr : Buffed.OperationMPtr := ctx.usize + (Buffed.OpResult.size * numResults)
  let ctx ← ctx.alloc size
  let ctx := ptr.writeNumOperands ctx numOperands admitted_bounds
  let ctx := ptr.writeNumResults ctx numResults admitted_bounds
  let ctx := ptr.writeNumBlockOperands ctx numBlockOperands admitted_bounds
  let ctx := ptr.writeNumRegions ctx numRegions admitted_bounds
  let ctx := ptr.writeParent ctx .none admitted_bounds
  let ctx := ptr.writeNext ctx .none admitted_bounds
  let ctx := ptr.writePrev ctx .none admitted_bounds
  some (ctx, ptr)

def Sim.OperationPtr.allocEmptySpec (ctx : Veir.IRContext OpInfo) (addr : Nat) (opType : OpInfo)
    (properties : HasOpInfo.propertiesOf opType) (capResults capBlockOperands capRegions capOperands : Nat)
    : Option (Veir.IRContext OpInfo × Veir.OperationPtr) :=
  OperationPtr.allocEmptyAt ctx opType properties addr capResults capBlockOperands capRegions capOperands

@[inline]
def Sim.OperationPtr.allocEmpty (ctx : Sim.IRContext OpInfo) (opType : OpInfo)
    (properties : HasOpInfo.propertiesOf opType)
    (numResults numOperands numBlockOperands numRegions : UInt64) :
    Option (Sim.OperationPtr × Sim.IRContext OpInfo) := do
  match allocEmptyImpl ctx.buf numResults numOperands numBlockOperands numRegions (Buffed.Operation.propertySize opType) with
  | none => none
  | some (ctxBuf, ptrImpl) =>
    let ⟨ctxSpec, ptrSpec⟩ := (allocEmptySpec ctx.spec ptrImpl.toNat opType properties
      numResults.toNat numBlockOperands.toNat numRegions.toNat numOperands.toNat).specGet!
    some ⟨⟨ptrImpl, ptrSpec⟩, ⟨ctxBuf, ctxSpec, admitted_sim ()⟩⟩

@[grind! .]
theorem Sim.OperationPtr.allocEmpty_spec {ctx : Sim.IRContext OpInfo} :
    allocEmpty ctx opType props c₁ c₂ c₃ c₄ = some ⟨ptr, ctx'⟩ →
    ∃ addr, Veir.OperationPtr.allocEmptyAt ctx.spec opType props c₁.toNat c₂.toNat c₃.toNat c₄.toNat addr = some ⟨ctx'.spec, ptr.spec⟩:= by
  unfold Sim.OperationPtr.allocEmpty
  -- TODO: we need to get from ctx.sim that the slot in the spec is free.
  sorry

theorem Veir.Sim.BlockPtr.getParent_impl2 {OpInfo : Type} [inst : HasOpInfo OpInfo] (ctx : Sim.IRContext OpInfo)
  (ptr : Sim.BlockPtr) (ib : ptr.InBounds ctx) :
  (Sim.BlockPtr.getParentSim ctx ptr ib).impl = Sim.BlockPtr.getParentImpl ctx.buf ctx.spec ⋯ ptr.impl ptr.spec ib := by
  unfold Sim.BlockPtr.getParentImpl
  unfold Sim.BlockPtr.getParentSim
  grind [Sim.OpOperandPtr, Sim.IRContext, Sim.ValuePtr, Sim.BlockArgumentPtr, Sim.BlockPtr, Sim.OperationPtr, Sim.BlockOperandPtr, Sim.OpResultPtr, Sim.RegionPtr, Sim.OpOperandPtrPtr, Sim.BlockOperandPtrPtr]
