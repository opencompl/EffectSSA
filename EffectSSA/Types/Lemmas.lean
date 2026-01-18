import EffectSSA.Types.WellTyped

/-!
# Lemmas about the typesystem
-/
namespace EffectSSA

/-!
## `grind` lemmas
--------------------------------------------------------------------------------
-/

@[simp, grind =]
theorem Program.wellTyped_nil_iff {Γ Δ : Context τ} :
    WellTypedWith Γ .nil Δ ↔ Γ = Δ := by
  grind [WellTypedWith]

@[simp, grind =]
theorem Program.wellTyped_cons_iff (i : Instruction τ) (p : Program τ) :
    WellTypedWith Γ (i ;> p) Ξ ↔ (∃ Δ, i.WellTyped Γ Δ ∧ p.WellTypedWith Δ Ξ) := by
  grind [WellTypedWith]

@[simp, grind =]
theorem Program.WellTyped_nil_iff {Γ : Context τ} :
    WellTyped Γ .nil ↔ Γ.isUnrestricted := by
  simp [Program.WellTyped]


open Instruction in attribute [grind ←]
  WellTyped.loadI
  WellTyped.storeI
  WellTyped.loadE
  WellTyped.storeE
  WellTyped.createEff
  WellTyped.consumeEff


/-!
## Uniqueness of out contexts
--------------------------------------------------------------------------------
-/

@[grind →]
theorem Instruction.WellTyped.unique
    {i : Instruction τ} {Δ Δ' : Context τ}
    (h₁ : i.WellTyped Γ Δ) (h₂ : i.WellTyped Γ Δ') :
      Δ = Δ' := by
  grind [WellTyped]

@[grind →]
theorem Program.WellTyped.unique
    {p : Program τ} {Δ Δ' : Context τ}
    (h₁ : p.WellTypedWith Γ Δ) (h₂ : p.WellTypedWith Γ Δ') :
      Δ = Δ' := by
  induction p generalizing Γ <;> grind

/-!
## Var
--------------------------------------------------------------------------------
-/
namespace Var

@[simp, grind =] theorem toNat_ofNat (i : Nat) : (Var.ofNat i).toNat = i := rfl
@[simp, grind =] theorem toNat_succ (v : Var) : v.succ.toNat = v.toNat + 1 := rfl

@[simp, grind =]
theorem inBounds_iff {v : Var} : v.InBounds Γ ↔ v.toNat < Γ.size := by rfl

end Var

/-!
## Context
--------------------------------------------------------------------------------
-/
namespace Context
variable {Γ : Context τ} {v : Var}

/-! ### size -/

@[simp, grind =] theorem size_empty : size (∅ : Context τ) = 0 := rfl
@[simp, grind =] theorem size_cons : size (Γ <: t) = Γ.size + 1 := rfl

/-! ### getElem -/

@[simp, grind =] theorem getElem_cons_zero : (Γ <: t)[Var.ofNat 0]'h = t := rfl
@[simp, grind =] theorem getElem_cons_succ :
    (Γ <: t)[v.succ]'h = Γ[v]'(by grind) := rfl

/-! ### isUnrestricted -/

@[simp, grind .] theorem isUnrestricted_empty : @isUnrestricted τ ∅ := by
  grind [isUnrestricted]

@[simp, grind =] theorem isUnrestricted_cons :
    (Γ <: t).isUnrestricted ↔ Γ.isUnrestricted ∧ t.isUnrestricted  := by
  unfold isUnrestricted Var.InBounds
  constructor
  · intro h
    and_intros
    · intro v
      have := h v.succ
      grind
    · have := h (Var.ofNat 0)
      grind
  · intro h v hv
    have : (v = Var.ofNat 0) ∨ (∃ (v' : Var), v = v'.succ) := by
      rcases v with _|i
      · left; rfl
      · right; use i; rfl
    rcases this with ⟨rfl, ⟨v, rfl⟩⟩ <;> grind

end Context
