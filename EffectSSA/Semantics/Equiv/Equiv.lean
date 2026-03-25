import EffectSSA.Syntax
import EffectSSA.Semantics.Equiv.ProgramContext
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas

/-!
# Program Equivalence
-/
namespace EffectSSA
open Semantics (ProgramContext TProgramContext)
variable {τ} [LawfulMemoryModel τ] {Γ Δ : Context τ}

/-
TODO: we might want to define equivalence of untyped programs as well, although
I'm not exactly sure how the obvious relation would behave when the programs are
mallformed, so it might not be an actual equivalence. In either case, if we do
define untyped equivalence, we should of course prove the relation with typed
equivalence.
-/

namespace TProgram

@[grind =]
def Equiv (p : TProgram Γ Δ) (q : TProgram Γ Δ) : Prop :=
  ∀ (C : TProgramContext Γ Δ), C.execProgram p = C.execProgram q

instance : Setoid (TProgram Γ Δ) where
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
variable {p q : TProgram Γ Δ}

/-- `_ ≈ _` is the preferred spelling -/
theorem equiv_iff : p.Equiv q ↔ p ≈ q := by rfl
