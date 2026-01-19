import EffectSSA.Types.WellTyped
import EffectSSA.Types.Simpset

/-!
# Lemmas about the typesystem
-/
namespace EffectSSA

/-!
## `grind` lemmas
--------------------------------------------------------------------------------
-/

/-! ### Program -/
namespace Program

@[simp, typecheck, grind =]
theorem wellTyped_nil_iff {Γ Δ : Context τ} :
    WellTypedWith Γ .nil Δ ↔ Γ = Δ := by
  grind [WellTypedWith]

@[simp, typecheck, grind =]
theorem wellTyped_cons_iff (i : Instruction τ) (p : Program τ) :
    WellTypedWith Γ (i ;> p) Ξ ↔ (∃ Δ, i.WellTyped Γ Δ ∧ p.WellTypedWith Δ Ξ) := by
  grind [WellTypedWith]

@[simp, typecheck, grind =]
theorem WellTyped_nil_iff {Γ : Context τ} :
    WellTyped Γ .nil ↔ Γ.isUnrestricted := by
  simp [Program.WellTyped]

end Program

/-! ### Program -/
namespace Instruction
open Ty.Typ (ptr eff data)
variable {Γ Δ : Context τ}

@[simp, typecheck, grind =]
theorem wellTyped_loadI_iff :
    WellTyped Γ (.loadI t p) Δ ↔ (Γ[p]? = some ptr ∧ Δ = Γ <: t) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_storeI_iff :
    WellTyped Γ (.storeI t p x) Δ
    ↔ (Γ[p]? = some ptr ∧ Γ[x]? = some (data t) ∧ Δ = Γ) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_loadE_iff :
    WellTyped Γ (.loadE t e p) Δ
    ↔ (Γ[e]? = some eff ∧ Γ[p]? = some ptr ∧ Δ = Γ.eraseVar e <: eff <: t) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_storeE_iff :
    WellTyped Γ (.storeE t e p x) Δ
    ↔ (Γ[e]? = some eff ∧ Γ[p]? = some ptr ∧ Γ[x]? = some (data t) ∧ Δ = Γ.eraseVar e <: eff) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_createEff_iff :
    WellTyped Γ .createEff Δ ↔ (Γ.isUnrestricted ∧ Δ = Γ <: eff) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_consumeEff_iff :
    WellTyped Γ (.consumeEff e) Δ
    ↔ (Γ[e]? = some eff ∧ (Γ.eraseVar e).isUnrestricted ∧ Δ = Γ.eraseVar e) := by
  grind [WellTyped]

end Instruction

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
    (Γ <: t)[v + 1]'h = Γ[v]'(by simp_all) := rfl

@[grind =]
theorem getElem_cons_eq :
    (Γ <: t)[v]'h =
      if hz : v = Var.ofNat 0 then
        t
      else
        Γ[v - 1]'(by simp_all; grind) := by
  match v with
  | .ofNat 0 => grind
  | .ofNat (i + 1) => simp; grind

@[simp, typecheck, grind =]
theorem getElem?_cons_zero : (Γ <: t)[Var.ofNat 0]? = some t := rfl
@[simp, typecheck, grind =]
theorem getElem?_cons_succ : (Γ <: t)[v + 1]? = Γ[v]? := rfl

/-! ### isUnrestricted -/

@[simp, typecheck, grind .] theorem isUnrestricted_empty : @isUnrestricted τ ∅ := by
  grind [isUnrestricted]

@[simp, typecheck, grind =] theorem isUnrestricted_cons :
    (Γ <: t).isUnrestricted ↔ Γ.isUnrestricted ∧ t.isUnrestricted  := by
  unfold isUnrestricted Var.InBounds
  constructor
  · intro h
    and_intros
    · intro v
      have := h (v + 1)
      grind
    · have := h (Var.ofNat 0)
      grind
  · intro h v hv
    have : (v = Var.ofNat 0) ∨ (∃ (v' : Var), v = v' + 1) := by
      rcases v with _ | i
      · left; rfl
      · right; use Var.ofNat i; rfl
    grind

/-! ### eraseVar -/

@[simp, typecheck, grind =]
theorem eraseVar_zero : (Γ <: t).eraseVar (Var.ofNat 0) = Γ := rfl

@[simp, typecheck, grind =]
theorem eraseVar_succ : (Γ <: t).eraseVar (v + 1) = Γ.eraseVar v <: t := rfl

end Context
