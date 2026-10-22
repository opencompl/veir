import Veir.InstSimplify.IS2406
namespace Veir.InstSimplify.IS2408
def pattern : Veir.Puddle.Pattern Veir.OpCode := IS2406.pattern true
theorem valid : Veir.Puddle.Pattern.Valid pattern := IS2406.valid true
end Veir.InstSimplify.IS2408
