module

public section

namespace Veir

@[extern "lean_internal_set_exit_on_panic"]
opaque setExitOnPanic (exit : Bool) : BaseIO Unit

def enableExitOnPanic : BaseIO Unit :=
  setExitOnPanic true

end Veir
