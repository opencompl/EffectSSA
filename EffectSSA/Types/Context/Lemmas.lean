import EffectSSA.Types.Context.Basic

import EffectSSA.Types.BasicLemmas
import EffectSSA.Types.Simpset

/-!
# Lemmas about `Context`s and `Var`iables.
-/
namespace EffectSSA

/-!
## Preliminary Context.ofList lemmas
--------------------------------------------------------------------------------
-/
namespace Context
variable {τ : Ty} (Γ : List τ.Typ) (v : Var)

@[simp, grind =] theorem getElem?_ofList : (ofList Γ)[v]? = Γ[v.toNat]? := by rfl
@[simp, grind =] theorem getElem_ofList (h) : (ofList Γ)[v]'h = Γ[v.toNat] := by rfl
@[simp, grind =] theorem size_ofList : (ofList Γ).size = Γ.length := by rfl

@[simp] theorem toList_ofList : (ofList Γ).toList = Γ := by rfl
-- FIXME: ^^ This ought to be a grind-lemma, but when tagged grind reports:
--           `invalid pattern, (non-forbidden) application expected #0`

@[simp, grind =] theorem ofList_toList (Γ : Context τ) : ofList Γ.toList = Γ := by rfl

end Context

/-!
## Var Lemmas
--------------------------------------------------------------------------------
-/
namespace Var
variable {v : Var}

theorem inBounds_iff_isSome : v.InBounds Γ ↔ Γ[v]?.isSome := by
  cases Γ; grind [InBounds]
theorem inBounds_iff_exists : v.InBounds Γ ↔ ∃ t, Γ[v]? = some t := by
  cases Γ; grind [inBounds_iff_isSome]
theorem inBounds_iff_lt_size : v.InBounds Γ ↔ v.toNat < Γ.size := by
  grind [InBounds]

@[grind .] theorem inBounds_of_isSome : Γ[v]?.isSome → v.InBounds Γ := by
  grind [inBounds_iff_isSome]

@[grind .] theorem inBounds_of_lt : v.toNat < Γ.size → v.InBounds Γ := by
  grind [InBounds]
@[grind →] theorem lt_size_of_inBounds : v.InBounds Γ → v.toNat < Γ.size := by
  grind [InBounds]

end Var


/-!
## Context
--------------------------------------------------------------------------------
-/
namespace Context
variable {Γ : Context τ} {v : Var}

/-! ### ext -/

theorem eq_of_toList {Γ Δ : Context τ} (h : Γ.toList = Δ.toList) : Γ = Δ := by
  cases Γ; cases Δ; grind

@[ext, grind ext]
theorem eq_of_getElem?_eq {Γ Δ : Context τ} (h : ∀ (v : Var), Γ[v]? = Δ[v]?) :
    Γ = Δ := by
  cases Γ; cases Δ
  apply eq_of_toList
  ext v
  grind [h ⟨v⟩]

/-! ### empty -/

@[simp, grind =] theorem getElem?_empty : (∅ : Context τ)[v]? = none := by rfl

/-! ### size -/

@[simp, grind =] theorem size_empty : size (∅ : Context τ) = 0 := rfl
@[simp, grind =] theorem size_cons : size (Γ <: t) = Γ.size + 1 := rfl

@[grind →]
theorem isSome_getElem?_of_inBounds : v.InBounds Γ → Γ[v]?.isSome := by
  cases Γ; grind

/-! ### getElem -/

@[simp, grind =] theorem getElem_cons_zero : (Γ <: t)[Var.ofNat 0]'h = t := rfl
@[simp, grind =] theorem getElem_cons_succ :
    (Γ <: t)[v + 1]'h = Γ[v]'(by grind) := rfl

@[grind =]
theorem getElem_cons_eq :
    (Γ <: t)[v]'h =
      if hz : v = Var.ofNat 0 then
        t
      else
        Γ[v - 1]'(by grind) := by
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

@[grind →] theorem isUnrestricted_eq_false_of_getElem (v : Var) :
    Γ[v]? = some .eff → Γ.isUnrestricted = false := by
  intro hv
  have hv : v.InBounds Γ := by grind
  have : (Γ[v]).isUnrestricted = false := by cases Γ; grind
  grind [isUnrestricted]

theorem isUnrestricted_iff_getElem? (Γ : Context τ) :
    Γ.isUnrestricted ↔ ∀ (v : Var), ∀ t ∈ Γ[v]?, t.isUnrestricted := by
  cases Γ; grind [isUnrestricted, Var.inBounds_iff_exists]

/-! ### eraseVar -/

@[simp, grind =] theorem toList_eraseVar :
  (Γ.eraseVar v).toList = Γ.toList.eraseIdx v.toNat := by rfl

@[simp, typecheck, grind =]
theorem eraseVar_zero : (Γ <: t).eraseVar (Var.ofNat 0) = Γ := rfl

@[simp, typecheck, grind =]
theorem eraseVar_succ : (Γ <: t).eraseVar (v + 1) = Γ.eraseVar v <: t := rfl

@[grind =]
theorem getElem?_eraseVar {w : Var} :
    (Γ.eraseVar v)[w]? = Γ[if w.toNat < v.toNat then w else w + 1]? := by
  rcases Γ with ⟨Γ⟩
  grind [eraseVar]

/-! ### eraseVar -/

@[simp, typecheck, grind =]
theorem eraseVars_nil : Γ.eraseVars [] = Γ := by rfl

end Context
