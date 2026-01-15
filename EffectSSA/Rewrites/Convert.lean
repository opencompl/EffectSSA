import EffectSSA.Syntax
import EffectSSA.Semantics

/-!
# Implicit to EffectSSA conversion rewrites
-/
namespace EffectSSA
namespace Rewrites
variable {τ}

-- theorem exec_createEff_consumeEff_eq :
