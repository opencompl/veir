module

public import Veir.IR.Buffed.ReservedOperation
public import Veir.IR.Buffed.Initialization
import all Veir.IR.Buffed.Basic

@[expose] public section
namespace Veir
open Buffed (countCard)
variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo]
set_option maxHeartbeats 1000000

theorem Sim.IRContext.reservation_disjoint (ctx : Sim.IRContext OpInfo)
    {b : Buffed.IRBufContext} {size address : UInt64}
    (h : ctx.buf.reserve size = some (b, address)) (p : TopLevelPtr) (hp : p.InBounds ctx.spec) :
    (p.range ctx.spec).upper ≤ address.toNat ∨
      (address.toNat : Int) + size.toNat ≤ (p.range ctx.spec).lower := by
  rcases Buffed.IRBufContext.reserve_origin h with ⟨free, ht, _⟩ | ⟨ha, _⟩
  · exact ctx.sim.free_disjoint size address (Buffed.FreeList.take_mem ht) p hp
  · have := ctx.sim.in_bounds p hp
    left
    rw [ha]
    simpa only [IsIncludedIN, ExArray.range_def] using this.2

theorem Sim.OperationPtr.reservation_fresh (ctx : Sim.IRContext OpInfo)
    {b : Buffed.IRBufContext} {size address ptr : UInt64}
    (h : ctx.buf.reserve size = some (b, address))
    (hlo : address.toNat ≤ ptr.toNat) (hhi : ptr.toNat + 72 ≤ address.toNat + size.toNat) :
    ¬ (⟨ptr.toNat⟩ : Veir.OperationPtr).InBounds ctx.spec := by
  intro hp
  have hd := ctx.reservation_disjoint h (.operation ⟨ptr.toNat⟩) hp
  simp only [TopLevelPtr.range, Veir.OperationPtr.range_ideal ctx.sim.repr hp,
    Veir.OperationPtr.rangeInt, Buffed.Operation.rangeInt, add_nat_range_def,
    Veir.OperationPtr.toFlat] at hd
  grind

end Veir
