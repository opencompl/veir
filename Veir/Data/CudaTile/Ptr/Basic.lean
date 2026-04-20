module

import Veir.ForLean


/-! ## Attribute definitions -/


/-!
  ## ToString implementation

  `ToString` is used to convert attributes to their MLIR textual representation.
  It is also the syntax used for printing attributes in the REPL and in error messages.
-/




/-!
  ## Coercion instances to Attribute

  We define a coercion from each attribute structure to `Attribute`.
-/

-- instance : Coe PointerType Attribute where
--   coe type := .pointerType type

-- instance : Coe PointerType TypeAttr where
--   coe type := ⟨.registerType type, by rfl⟩
