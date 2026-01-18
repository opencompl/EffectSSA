import EffectSSA.Syntax
import EffectSSA.Semantics
import EffectSSA.Rewrites.Basic

/-!
# Implicit to EffectSSA conversion rewrites
-/
namespace EffectSSA
namespace Rewrites
variable {τ}

def createEff_consumeEff : Rewrite τ where
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
  simp only [Program.results_nil, Fin.isValue, Program.results_cons]
  sorry

end createEff_consumeEff
