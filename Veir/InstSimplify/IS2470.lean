import Veir.InstSimplify.IS2468
namespace Veir.InstSimplify.IS2470
def pattern : Veir.Puddle.Pattern Veir.OpCode := IS2468.pattern true
theorem valid : Veir.Puddle.Pattern.Valid pattern := IS2468.valid true
end Veir.InstSimplify.IS2470
