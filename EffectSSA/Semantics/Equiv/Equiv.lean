import EffectSSA.Syntax
import EffectSSA.Semantics.Equiv.ClosingContext
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas

/-!
# Program Equivalence
-/
namespace EffectSSA
namespace Program

@[grind =]
def Equiv (p : Program τ) (q : Program τ) : Prop :=
  -- TODO: this is just a placeholder, the actual definition should
  -- refer to contexts
  p = q

instance : Setoid (Program τ) where
  r := Equiv
  iseqv := {
    refl := by grind
    symm := by grind
    trans := by grind
  }

/-!
## Lemmas
--------------------------------------------------------------------------------
-/
section Lemmas
variable {p q : Program τ}

/-- `_ ≈ _` is the preferred spelling -/
theorem equiv_iff : p.Equiv q ↔ p ≈ q := by rfl
