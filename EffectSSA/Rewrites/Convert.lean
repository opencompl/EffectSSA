import EffectSSA.Syntax
import EffectSSA.Semantics
import EffectSSA.Rewrites.Basic

/-!
# Implicit to EffectSSA conversion rewrites
-/
namespace EffectSSA
namespace Rewrites
variable {τ}

def createEff_consumeEff : Rewrite τ 0 where
  src := {
    program := program!()
    returnVars := []
  }
  tgt := {
    program := program!(
      e := createEff;
      consumeEff(e)
    )
    returnVars := []
  }

namespace createEff_consumeEff

theorem welltyped : (@createEff_consumeEff τ).WellFormed ∅ := by
  use []
  unfold createEff_consumeEff
  decide

end createEff_consumeEff
