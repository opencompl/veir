module

public import Veir.Buffered.IR.Buffed.RawAccessors
public import Veir.Buffered.IR.Buffed.Sim
public import Veir.Buffered.IR.Buffed.SimDefs

public section

namespace Veir.Buffered.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] [HasBuffedOpCode OpInfo] {ctx : Sim.IRContext OpInfo}

@[local ext, local grind ext]
theorem _root_.Veir.Buffered.OpResultPtr.ext (x y : OpResultPtr) : x.op = y.op → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

@[local ext, local grind ext]
theorem _root_.Veir.Buffered.BlockArgumentPtr.ext (x y : BlockArgumentPtr) : x.block = y.block → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

end read_write

end Veir.Buffered.Buffed
