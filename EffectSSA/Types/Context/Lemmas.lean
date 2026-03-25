import EffectSSA.Types.Context.Basic

import EffectSSA.Types.BasicLemmas
import EffectSSA.Types.Simpset

/-!
# Lemmas about `Context`s and `Var`iables.
-/
namespace EffectSSA

/-!
## Preliminary Context.ofList & Context.toList lemmas
--------------------------------------------------------------------------------
-/
namespace Context
variable {τ : Ty} (v : Var) (Γ : Context τ)

@[simp, grind =] theorem get?_eq : Γ.get? v = Γ[v]? := by rfl
@[grind =] theorem getElem_eq : Γ[v]'h = Γ[v]?.get h := by rfl

section OfList
variable (Γ : List (Option τ.Typ))

@[simp, grind =] theorem getElem?_ofList : (ofList Γ)[v]? = Γ[v.toNat]?.join := by rfl
@[grind =] theorem getElem_ofList : (ofList Γ)[v]'h = Γ[v.toNat]?.join.get h := by rfl
@[simp, grind =] theorem size_ofList : (ofList Γ).size = Γ.length := by rfl

@[simp] theorem toList_ofList : (ofList Γ).toList = Γ := by rfl
-- FIXME: ^^ This ought to be a grind-lemma, but when tagged grind reports:
--           `invalid pattern, (non-forbidden) application expected #0`

end OfList
section ToList
variable (Γ : Context τ)

@[simp, grind =] theorem ofList_toList : ofList Γ.toList = Γ := by rfl

@[simp, grind =] theorem toList_empty : toList (∅ : Context τ) = [] := by rfl
@[simp, grind =] theorem toList_snoc : toList (Γ <: t) = some t :: Γ.toList := by rfl
@[simp, grind =] theorem toList_snocStale : toList (Γ.snocStale) = none :: Γ.toList := by rfl

end ToList
end Context

/-!
## Var Lemmas
--------------------------------------------------------------------------------
-/
namespace Var
variable {v : Var}


@[grind →] theorem lt_size_of_liveIn : v.LiveIn Γ → v.toNat < Γ.size := by
  grind [LiveIn, Context.get?]

instance : Decidable (v.LiveIn Γ) := by unfold LiveIn; infer_instance

end Var

/-!
## Induction Principles
--------------------------------------------------------------------------------
-/

@[elab_as_elim, induction_eliminator]
def Context.recOn' {motive : Context τ → Sort u}
    (Γ : Context τ)
    (empty : motive ∅)
    (snocStale : ∀ Γ, motive Γ → motive (snocStale Γ))
    (snoc : ∀ Γ t, motive Γ → motive (Γ <: t)) :
    motive Γ :=
  go Γ.toList
where
  go : (Γ : List _) → motive ⟨Γ⟩
  | [] => empty
  | none :: Γ => snocStale ⟨Γ⟩ (go Γ)
  | some t :: Γ => snoc ⟨Γ⟩ t (go Γ)

@[elab_as_elim, cases_eliminator]
def Context.casesOn' {motive : Context τ → Sort u}
    (Γ : Context τ)
    (empty : motive ∅)
    (snocStale : ∀ Γ, motive (snocStale Γ))
    (snoc : ∀ Γ t, motive (Γ <: t)) :
    motive Γ :=
  recOn' Γ empty (fun Γ _ => snocStale Γ) (fun Γ t _ => snoc Γ t)

@[elab_as_elim, induction_eliminator]
def Var.recOn' {motive : Var → Sort u}
    (v : Var)
    (zero : motive ⟨0⟩)
    (succ : ∀ v, motive v → motive (v + 1)) :
    motive v :=
  go v.toNat
where
  go : (v : Nat) → motive ⟨v⟩
  | 0 => zero
  | v + 1 => succ ⟨v⟩ (go v)

@[elab_as_elim, cases_eliminator]
def Var.casesOn' {motive : Var → Sort u}
    (v : Var)
    (zero : motive ⟨0⟩)
    (succ : ∀ (v : Var), motive (v + 1)) :
    motive v :=
  recOn' v zero (fun v _ => succ v)

/-!
## Context
--------------------------------------------------------------------------------
-/
namespace Context
variable {Γ : Context τ} {v : Var}

/-! ### ext -/

theorem eq_of_toList {Γ Δ : Context τ} (h : Γ.toList = Δ.toList) : Γ = Δ := by
  rcases Γ; rcases Δ; grind

@[ext, grind ext]
theorem eq_of_getElem?_eq {Γ Δ : Context τ}
    (h_size : Γ.size = Δ.size)
    (h_get : ∀ (v : Var), Γ[v]? = Δ[v]?) :
    Γ = Δ := by
  rcases Γ; rcases Δ
  apply eq_of_toList
  ext v
  grind [h_get ⟨v⟩]

/-! ### empty -/

@[simp, grind =] theorem getElem?_empty : (∅ : Context τ)[v]? = none := by rfl

/-! ### size -/

@[simp, grind =] theorem size_empty : size (∅ : Context τ) = 0 := rfl
@[simp, grind =] theorem size_snoc : size (Γ <: t) = Γ.size + 1 := rfl

/-! ### getElem -/

/-- When `v` is a known live variable, `Γ[v]?` is `some (Γ[v]'h)`. -/
@[grind =]
theorem getElem?_eq_some_getElem {v : Var} {Γ : Context τ} (h : v.LiveIn Γ) :
    Γ[v]? = some (Γ[v]'h) := by
  grind

/-! ### getElem? -/

@[grind =] theorem getElem?_snoc :
    (Γ <: t)[v]? = if v = Var.ofNat 0 then some t else Γ[v - 1]? := by
  cases v <;> rfl

@[simp, typecheck, grind =]
theorem getElem?_snoc_zero : (Γ <: t)[Var.ofNat 0]? = some t := rfl
@[simp, typecheck, grind =]
theorem getElem?_snoc_succ : (Γ <: t)[v + 1]? = Γ[v]? := rfl

@[grind =]
theorem getElem?_snocStale :
    Γ.snocStale[v]? = if v = Var.ofNat 0 then none else Γ[v - 1]? := by
  cases v <;> rfl

@[simp, typecheck, grind =]
theorem getElem?_snocStale_zero : Γ.snocStale[Var.ofNat 0]? = none := rfl
@[simp, typecheck, grind =]
theorem getElem?_snocStale_succ : Γ.snocStale[v + 1]? = Γ[v]? := rfl

end Context
-- ^^ We have to close the section to avoid the following instance from picking
--    up unneccesary variables, that for some reason are being put in the
--    instance even when explicitly `omit`ed.

instance : LawfulGetElem (Context τ) Var τ.Typ _ where
  getElem?_def Γ v _ := by
    by_cases h : v.LiveIn Γ
    · grind
    · suffices Γ[v]? = none by grind
      simpa [Var.LiveIn] using h

namespace Context
variable {Γ : Context τ} {v : Var}

/-! ### isUnrestricted -/

@[simp, typecheck, grind .] theorem isUnrestricted_empty : @isUnrestricted τ ∅ := by
  grind [isUnrestricted]

@[simp, typecheck, grind =] theorem isUnrestricted_snocStale :
    Γ.snocStale.isUnrestricted ↔ Γ.isUnrestricted := by
  constructor
  · intro h v t ht
    apply h (v + 1)
    grind
  · grind [isUnrestricted]

@[simp, typecheck, grind =] theorem isUnrestricted_snoc :
    (Γ <: t).isUnrestricted ↔ Γ.isUnrestricted ∧ t.isUnrestricted := by
  by_cases h : Γ.isUnrestricted ∧ t.isUnrestricted
  · suffices (Γ <: t).isUnrestricted by grind
    grind [isUnrestricted]
  · suffices ¬(Γ <: t).isUnrestricted by grind
    suffices ∃ (v : Var) (t' : τ.Typ), (Γ <: t)[v]? = some t' ∧ ¬t'.isUnrestricted by
      grind [isUnrestricted]
    replace h : ¬t.isUnrestricted ∨ ¬Γ.isUnrestricted := by grind
    rcases h with h|h
    · use Var.ofNat 0, t; grind
    · obtain ⟨v, t', h⟩ : ∃ (v : Var) (t' : τ.Typ), Γ[v]? = some t' ∧ ¬t'.isUnrestricted := by
        grind [isUnrestricted]
      use v + 1; grind

@[grind →] theorem isUnrestricted_eq_false_of_getElem (v : Var) :
    Γ[v]? = some .eff → Γ.isUnrestricted = false := by
  grind [isUnrestricted]


/-! ### eraseVar -/

@[simp, grind =] theorem toList_eraseVar :
  (Γ.eraseVar v).toList = Γ.toList.set v.toNat none := by rfl

@[simp, typecheck, grind =]
theorem eraseVar_zero : (Γ <: t).eraseVar (Var.ofNat 0) = Γ.snocStale := rfl

@[simp, typecheck, grind =]
theorem eraseVar_succ : (Γ <: t).eraseVar (v + 1) = Γ.eraseVar v <: t := rfl

@[simp, typecheck, grind =]
theorem empty_eraseVar : (∅ : Context τ).eraseVar v = ∅ := by rfl

@[grind =]
theorem snocStale_eraseVar :
    Γ.snocStale.eraseVar v
    = (if v = Var.ofNat 0 then Γ else Γ.eraseVar (v - 1)).snocStale := by
  grind [eraseVar, snocStale]

@[grind =]
theorem getElem?_eraseVar {w : Var} : (Γ.eraseVar v)[w]? = if v = w then none else Γ[w]? := by
  rcases Γ with ⟨Γ⟩; grind [eraseVar]

/-! ### eraseVars -/

@[simp, typecheck, grind =]
theorem eraseVars_nil : Γ.eraseVars [] n = Γ := by rfl

@[simp, typecheck, grind =]
theorem eraseVars_cons : Γ.eraseVars (v :: vs) n = (Γ.eraseVars vs n).eraseVar (v + n) := by rfl

/-- Erasing variables only marks them as stale, it does _not_ change the size of the context. -/
@[simp, grind =] theorem size_eraseVars : (Γ.eraseVars vs n).size = Γ.size := by
  induction vs <;> grind

@[grind =]
theorem getElem?_eraseVars {w : Var} :
    (Γ.eraseVars vs n)[w]? = if w.toNat ≥ n ∧ (w - n) ∈ vs then none else Γ[w]? := by
  induction vs <;> grind

@[simp, grind =]
theorem getElem?_eraseVars' {w : Var} :
    (Γ.eraseVars vs)[w]? = if w ∈ vs then none else Γ[w]? := by
  have : w - 0 = w := by rfl
  grind

@[simp, typecheck, grind =]
theorem empty_eraseVars : (∅ : Context τ).eraseVars vs = ∅ := by grind

@[grind .]
theorem getElem?_eraseVars_of_getElem? {v : Var} (hΓ : Γ[v]? = some t) (hv : v ∉ vs) :
    (Γ.eraseVars vs)[v]? = some t := by
  grind

@[grind .] theorem getElem?_of_getElem?_eraseVars :
    (Γ.eraseVars vs)[v]? = some t → (∃ w ∉ vs, Γ[w]? = some t) := by
  grind

end Context

/-!
## Decidability
-/

/-- Unrestrictedness of a context is decidable. -/
instance {τ} {Γ : Context τ} : Decidable (Γ.isUnrestricted) :=
  decidable_of_bool (Γ.toList.all (fun t => t.all (·.isUnrestricted))) <| by
    induction Γ <;> grind
