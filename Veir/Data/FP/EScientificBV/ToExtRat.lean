module

public import Veir.Data.FP.EScientificBV
public import Veir.Data.FP.ExtRat

namespace Veir.Data.FP.EScientificBV

public section


def toExtRat {e s : Nat} : EScientificBV e s → ExtRat
  | .zero sign => .number 0
  | .nonzeroFinite sbv => .number sbv.toRat
  | .infinity sign => .infinity sign
  | .nan => none

  end -- public section

