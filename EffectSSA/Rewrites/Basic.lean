import EffectSSA.Syntax
import EffectSSA.Semantics
import EffectSSA.Types

/-!
# Rewrite data structure
-/
namespace EffectSSA

/-!
## Data Structures
--------------------------------------------------------------------------------
-/

/--
A rewrite consists of two program fragments.
-/
structure Rewrite τ where
  src : Program τ
  tgt : Program τ

/-!
## Wellformedness Constraints
--------------------------------------------------------------------------------
-/

open Program (WellTyped)

/--
A rewrite is wellformed, if both fragments are welltyped, under the same context
and with the same expected return types.
-/
@[grind =]
def Rewrite.WellFormed (Γ : Context τ) (r : Rewrite τ) : Prop :=
  ∃ ts, WellTyped Γ r.src ts ∧ WellTyped Γ r.tgt ts

/-!
## Semantics Correctness Constraints
--------------------------------------------------------------------------------
-/
variable {τ} [MemoryModel τ]

/--
A rewrite is correct, if the source and target fragments are equivalent.
-/
def Rewrite.Correct (r : Rewrite τ) : Prop :=
  r.src ≈ r.tgt


/-!
## Lemmas
--------------------------------------------------------------------------------
-/

-- /--
-- Only wellformed rewrites can be correct
-- -/
-- theorem Rewrite.wellFormed_of_correct (h : Correct r) : ∃ Γ, WellFormed Γ r := by
--   -- TODO: this does not actually hold under the current placeholder definition
--   -- of program equivalence, but it likely should hold under the actual eventual
--   -- definition
--   sorry
