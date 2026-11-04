import Veir.Parser.AttrParser

/-! Attribute tests for the original buffered model. In particular, its FloatType records
only a width; these are not the upstream vector/tensor or bit-precise FP tests. -/

namespace UnitTest.AttrParser
open Veir Veir.Parser Veir.AttrParser

def readType (text : String) (state : AttrParserState := {}) : Except ParserError TypeAttr := do
  let parser ← ParserState.fromInput text.toUTF8
  parseType.run' state parser

def readAttr (text : String) (state : AttrParserState := {}) : Except ParserError Attribute := do
  let parser ← ParserState.fromInput text.toUTF8
  parseAttribute.run' state parser

#guard readType "i32" == .ok (IntegerType.mk 32)
#guard readType "i0" == .ok (IntegerType.mk 0)
#guard readType "f64" == .ok (FloatType.mk 64)
#guard !(readType "not_a_type").isOk
#guard !(readType "!missing").isOk
#guard !(readAttr "i0x4").isOk
#guard readAttr "i32" == .ok (.integerType ⟨32⟩)
#guard readAttr "42 : i32" == .ok (.integerAttr ⟨42, ⟨32⟩⟩)
#guard readAttr "-1 : i32" == .ok (.integerAttr ⟨-1, ⟨32⟩⟩)
#guard readAttr "1.5 : f64" == .ok (.floatAttr ⟨1.5, ⟨64⟩⟩)
#guard readAttr "\"hello\"" == .ok (.stringAttr ⟨"hello".toUTF8⟩)
#guard readAttr "unit" == .ok (.unitAttr ⟨⟩)
#guard readAttr "@target" == .ok (.flatSymbolRefAttr ⟨"@target"⟩)
#guard readAttr "array<i32: 1, 2, 3>" == .ok (.denseArrayAttr ⟨⟨32⟩, #[1, 2, 3]⟩)
#guard (readAttr "[1 : i32, 2 : i32]").isOk
#guard (readAttr "{count = 42 : i32}").isOk
#guard (readType "!llvm.ptr").isOk
#guard (readType "!llvm.array<4 x i32>").isOk
#guard (readType "(i32) -> i64").isOk
#guard !(readType "!unknown.type").isOk
#guard (readType "!unknown.type" { allowUnregisteredDialect := true }).isOk

private def aliases : AttrParserState :=
  { typeAliases := ({} : Std.HashMap ByteArray TypeAttr).insert "word".toUTF8 (IntegerType.mk 32) }

#guard readType "!word" aliases == .ok (IntegerType.mk 32)
#guard readAttr "42 : !word" aliases == .ok (.integerAttr ⟨42, ⟨32⟩⟩)

end UnitTest.AttrParser
