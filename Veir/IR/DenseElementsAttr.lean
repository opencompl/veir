module

public import Veir.IR.Attribute
import Veir.ForLean

namespace Veir

/--
  Decode a raw dense elements body, `"0x..."`, as `count` unsigned `width`-bit patterns.
  As in MLIR's `DenseElementsAttr::getFromRawBuffer`, each element takes
  `⌈width / 8⌉` little-endian bytes, and a buffer holding a single element is a splat.
  The caller checks the attribute's shape and supplies its element count and integer width.
  Returns `none` for malformed hex or a buffer whose size fits neither form.
-/
public def DenseElementsAttr.parseRawIntegers? (body : String) (count width : Nat) :
    Option (Array Nat) := do
  let digits ← (body.dropPrefix? "\"0x").bind (·.dropSuffix? "\"")
  let digits ← digits.toString.toList.toArray.mapM Char.hexDigit?
  guard (digits.size % 2 == 0)
  let bytes := (Array.range (digits.size / 2)).map fun i =>
    digits[2 * i]!.toNat * 16 + digits[2 * i + 1]!.toNat
  let stride := (width + 7) / 8
  let element (i : Nat) : Nat :=
    (List.range stride).foldr (fun j acc => acc * 256 + bytes[i * stride + j]!) 0 % 2 ^ width
  if bytes.size == stride then
    return Array.replicate count (element 0)
  guard (bytes.size == stride * count)
  return (Array.range count).map element

end Veir
