import EffectSSA.Types.WellTyped

/-!
# Lemmas about the typesystem
-/
namespace EffectSSA

/-!
## `grind` annotations
--------------------------------------------------------------------------------
-/

@[simp, grind =]
theorem Program.wellTyped_nil_iff {Γ : Context τ n} {Δ : Context τ m} :
    WellTypedWith Γ (.nil) Δ ↔ ∃ (h : n = m), h ▸ Γ = Δ := by
  grind [Program.WellTypedWith]

@[simp, grind =]
theorem Program.wellTyped_cons_iff (i : Instruction τ n) (p : Program τ i.results) :
    WellTypedWith Γ (i ;> p) Ξ ↔ (∃ Δ, i.WellTyped Γ Δ ∧ p.WellTypedWith Δ Ξ) := by
  grind [Program.WellTypedWith]

open Instruction in attribute [grind ←]
  WellTyped.loadI
  WellTyped.storeI
  WellTyped.loadE
  WellTyped.storeE
  WellTyped.createEff
  WellTyped.consumeEff

open Program in attribute [grind →]
  -- WellTypedWith.nil
  WellTypedWith.cons

-- WellTypedWith ?_ (.nil) ?_
-- WellTypedWith ?_ (.cons ?_ ?_) ?_

/-!
## Uniqueness of out contexts
--------------------------------------------------------------------------------
-/

theorem Instruction.WellTyped.unique
    {i : Instruction τ n} {Δ : Context τ m} {Δ' : Context τ m'}
    (h₁ : i.WellTyped Γ Δ) (h₂ : i.WellTyped Γ Δ') :
      ∃ (h : m = m'), Δ = h ▸ Δ' := by
  grind

theorem Program.WellTyped.unique
    {p : Program τ n} {Δ : Context τ m} {Δ' : Context τ m'}
    (h₁ : p.WellTypedWith Γ Δ) (h₂ : p.WellTypedWith Γ Δ') :
      ∃ (h : m = m'), Δ = h ▸ Δ' := by
  induction p <;> (cases h₁; cases h₂)
  · use rfl
  · grind
