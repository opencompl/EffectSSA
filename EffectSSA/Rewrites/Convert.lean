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

macro "typecheck" : tactic => `(tactic|(
  simp -failIfUnchanged only [
    typecheck,
    ProgramFragment.WellTyped, Program.WellTyped,
    Context.isUnrestricted_empty,
    List.length_nil,
    ↓existsAndEq, and_true, true_and,
  ]
  grind
))

theorem welltyped : (@createEff_consumeEff τ).WellFormed ∅ := by
  use []
  unfold createEff_consumeEff
  typecheck

end createEff_consumeEff
