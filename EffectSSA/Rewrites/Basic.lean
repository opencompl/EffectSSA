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

-- TODO: ProgramFragment.append
-- TODO: ProgramFragment.execClosed

/--
A rewrite is correct, if the source and target fragments compute the same values
for the return variables (given the same environment).
-/
def Rewrite.Correct (r : Rewrite τ) : Prop :=
  ∃ (Δ : Context τ) (ts : _),
    r.src.WellTyped Δ ts
    ∧ r.tgt.WellTyped Δ ts
    ∧ ∀ (C : Program τ), C.WellTyped ∅ Δ.toList →
          (C ++ r.src).execClosed? = (C ++ r.tgt).execClosed?
  -- FIXME: this is actually too granular, as it looks for strict equality of
  --        of traces, whereas we want to consider something a bit looser, e.g.
  --        to disregard the specific order of load events.
  -- ∀ {env} {Γ}, env.WellTyped Γ → r.src.exec env = r.tgt.exec env
