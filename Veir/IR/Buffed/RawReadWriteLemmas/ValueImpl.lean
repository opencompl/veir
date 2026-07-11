module

public import Veir.IR.Buffed.RawAccessors
public import Veir.IR.Buffed.Sim
public import Veir.IR.Buffed.SimDefs

public section

namespace Veir.Buffed

section read_write

variable [HasOpInfo OpInfo] [SerializableOpInfo OpInfo] {ctx : Sim.IRContext OpInfo}

@[local ext, local grind ext]
theorem _root_.Veir.OpResultPtr.ext (x y : OpResultPtr) : x.op = y.op → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

@[local ext, local grind ext]
theorem _root_.Veir.BlockArgumentPtr.ext (x y : BlockArgumentPtr) : x.block = y.block → x.index = y.index → x = y := by
  rcases _ : x
  rcases _ : y
  grind

end read_write

end Veir.Buffed
