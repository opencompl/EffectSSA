import EffectSSA.Syntax.Untyped
import EffectSSA.Semantics
import EffectSSA.Rewrites.Basic

import EffectSSA.Tactic

/-!
# Implicit to EffectSSA conversion rewrites
-/
namespace EffectSSA
open Semantics (TProgramContext)
namespace Rewrites

variable {τ}

def createEff_consumeEff : TRewrite (τ:=τ) ∅ [] where
  rSrc := {
    instructions := program!()
    returnVars := []
  }
  rTgt := {
    instructions := program!(
      e := createEff;
      consumeEff(e)
    )
    returnVars := []
  }

namespace createEff_consumeEff


/-!
## Contextual Equivalence

We actually *do* need contextual equivalence to show this, given the current
interpretation of `createEff` / `consumeEff` as being UB when called multiple
(unbalanced) times.

That is, because the `takeTrace_putTrace` rewrite only actually holds when the
current trace state is not none. This is in fact guaranteed by the wellformedness
condition, as it would only be none if `createEff` was already called somewhere
earlier in the program without `consumeEff` following it, but in this scenario
we would *not* have an unrestricted context, and thus the current program would
not be welltyped.

-/

variable [MemoryModel τ]
theorem correct : (@createEff_consumeEff τ).Correct := by
  intro C
  simp [TProgramContext.execProgram]


  stop
  use ∅, []
  and_intros <;> (try typecheck)
  simp
  apply StateT.ext
  intro s
  have : ¬s.isNone := by
    -- Here we would have to use contextual equivalence reasoning to actually
    -- establish this
    sorry
  rcases s with _|es
  · contradiction
  · simp [ProgramFragment.exec, Instruction.exec]

end createEff_consumeEff
