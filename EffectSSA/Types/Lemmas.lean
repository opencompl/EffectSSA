import EffectSSA.Types.WellTyped

/-!
# Lemmas about the typesystem
-/
namespace EffectSSA

/-! ### `grind` annotation of the constructors -/

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
