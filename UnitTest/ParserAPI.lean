module

import Veir

/-! Check the public parser API through the library root. Native execution lives in
`parser-tests`, since ExArray's static C FFI is unavailable to `#eval`. -/

public section
namespace UnitTest.ParserAPI

private def source : ByteArray := r#"
"builtin.module"() ({
  "test.test"(%later) : (i32) -> ()
  %later = "test.test"() : () -> i32
}) : () -> ()
"#.toUTF8

def testParser : IO Unit := do
  match Veir.Parser.parseSourceString source with
  | .error error => throw (IO.userError s!"buffered parser: {error}")
  | .ok _ => pure ()

example {content : ByteArray} {ctx : Veir.Parser.StaticIR.Context}
    {op : Veir.Parser.IR.Op} {info : Veir.Parser.SourceInfo}
    (h : Veir.Parser.parseSourceString content = .ok (ctx, op, info)) :
    ctx.spec.WellFormed ∧ op.InBounds ctx.toIRContext :=
  Veir.Parser.parseSourceString_safe h

end UnitTest.ParserAPI
