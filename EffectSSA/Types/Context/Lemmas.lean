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

@[grind =] theorem eq_get? : Γ.toList[v.toNat]?.join = Γ[v]? := by rfl

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

@[simp, grind =] theorem toList_take (Γ : Context τ) (n : Nat) : (Γ.take n).toList = Γ.toList.take n := by rfl
@[simp, grind =] theorem toList_drop (Γ : Context τ) (n : Nat) : (Γ.drop n).toList = Γ.toList.drop n := by rfl

@[simp, grind =] theorem toList_append (Γ Δ : Context τ) : toList (Γ ++ Δ) = Δ.toList ++ Γ.toList := by rfl

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

@[simp] theorem not_liveIn_empty : ¬v.LiveIn (∅ : Context τ) := by
  grind [LiveIn, Context.get?]

@[simp, grind =] theorem liveIn_snoc :
    v.LiveIn (Γ <: t) ↔ v = Var.ofNat 0 ∨ (v - 1).LiveIn Γ := by
  cases v; grind [LiveIn, Context.get?]

@[simp, grind =] theorem liveIn_snocStale :
    v.LiveIn Γ.snocStale ↔ v ≠ Var.ofNat 0 ∧ (v - 1).LiveIn Γ := by
  cases v; grind [LiveIn, Context.get?]

@[simp, grind =] theorem liveIn_append :
    v.LiveIn (Γ ++ Δ) ↔ v.LiveIn Δ ∨ (¬v.toNat < Δ.size ∧ (v - Δ.size).LiveIn Γ) := by
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
@[simp, grind =] theorem size_snocStale : size Γ.snocStale = Γ.size + 1 := rfl
@[simp, grind =] theorem size_append (Γ Δ : Context τ) : (Γ ++ Δ).size = Γ.size + Δ.size := by
  simp [size, toList_append, Nat.add_comm]

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

/-! ### snoc_inj -/

@[simp, grind =] theorem snoc_inj {Γ Γ' : Context τ} {t t' : τ.Typ} :
    Γ <: t = Γ' <: t' ↔ Γ = Γ' ∧ t = t' := by
  constructor
  · intro h; grind [eq_of_toList, congr_arg toList h]
  · grind

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

/-- Erasing variables only marks them as stale, it does _not_ change the size of the context. -/
@[simp, grind =] theorem size_eraseVar : (Γ.eraseVar v).size = Γ.size := by
  grind

@[simp, grind =] theorem liveIn_eraseVar :
    v.LiveIn (Γ.eraseVar w) ↔ (v ≠ w ∧ v.LiveIn Γ) := by
  grind [Var.LiveIn]

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

@[simp, grind =] theorem liveIn_eraseVars :
    v.LiveIn (Γ.eraseVars ws) ↔ (v ∉ ws ∧ v.LiveIn Γ) := by
  grind [Var.LiveIn]

@[simp, grind =] theorem eraseVar_eraseVar (Γ : Context τ) (v w : Var) :
    (Γ.eraseVar v).eraseVar w = (Γ.eraseVar w).eraseVar v := by
  grind [eraseVar]

@[simp, grind =] theorem eraseVar_eraseVar_same (Γ : Context τ) (v : Var) :
    (Γ.eraseVar v).eraseVar v = Γ.eraseVar v := by
  grind [eraseVar]

/-! ### set -/

@[simp, grind =] theorem size_set : (Γ.set v t).size = Γ.size := by grind [set]

@[simp, grind =] theorem eraseVar_set_same : (Γ.set v t).eraseVar v = Γ.eraseVar v := by
  grind [set, eraseVar]

@[grind =] theorem getElem?_set : (Γ.set v t)[w]? = if v = w then (if v.toNat < Γ.size then t else none) else Γ[w]? := by
  grind [set]

/-! ### append -/

@[simp, grind =] theorem append_empty : (Γ ++ ∅) = Γ := by rfl
@[simp, grind =] theorem empty_append : (∅ ++ Γ) = Γ := by
  apply eq_of_toList; grind

@[simp, grind =] theorem append_snoc : Γ ++ (Δ <: t) = (Γ ++ Δ) <: t := by rfl
@[simp, grind =] theorem append_snocStale : Γ ++ Δ.snocStale = (Γ ++ Δ).snocStale := by rfl

@[simp, grind =] theorem append_assoc : (Γ ++ Δ) ++ Ξ = Γ ++ (Δ ++ Ξ) := by
  apply eq_of_toList; grind

@[simp, grind =] theorem getElem?_append {v : Var} {Γ Δ : Context τ} :
    (Γ ++ Δ)[v]? = if v.toNat < Δ.size then Δ[v]? else Γ[v - Δ.size]? := by
  rw [← eq_get?]; grind

@[grind =] theorem eraseVar_append (Γ Δ : Context τ) (v : Var) :
    (Γ ++ Δ).eraseVar v =
      if v.toNat < Δ.size then Γ ++ Δ.eraseVar v else Γ.eraseVar (v - Δ.size) ++ Δ := by
  grind

/-! ### take/drop -/

@[simp, grind =] theorem take_zero : (Γ : Context τ).take 0 = ∅ := by rfl
@[simp, grind =] theorem drop_zero : (Γ : Context τ).drop 0 = Γ := by rfl

@[simp, grind =] theorem snoc_take_succ : (Γ <: t).take (n + 1) = Γ.take n <: t := by rfl
@[simp, grind =] theorem snoc_drop_succ : (Γ <: t).drop (n + 1) = Γ.drop n := by rfl

@[simp, grind =] theorem snocStale_take_succ : Γ.snocStale.take (n + 1) = (Γ.take n).snocStale := by rfl
@[simp, grind =] theorem snocStale_drop_succ : Γ.snocStale.drop (n + 1) = Γ.drop n := by rfl

@[simp, grind =] theorem empty_take : (∅ : Context τ).take n = ∅ := by grind [take]
@[simp, grind =] theorem empty_drop : (∅ : Context τ).drop n = ∅ := by grind [drop]

@[simp, grind =] theorem size_take (Γ : Context τ) (n : Nat) : (Γ.take n).size = min n Γ.size := by
  simp [size, take, List.length_take]
@[simp, grind =] theorem size_drop (Γ : Context τ) (n : Nat) : (Γ.drop n).size = Γ.size - n := by
  simp [size, drop, List.length_drop]

@[simp, grind =] theorem getElem?_take {v : Var} {n : Nat} :
    (Γ.take n)[v]? = if v.toNat < n then Γ[v]? else none := by
  grind [take]

@[simp, grind =] theorem getElem?_drop {v : Var} {n : Nat} :
    (Γ.drop n)[v]? = Γ[v + n]? := by
  grind [drop]

@[simp, grind =] theorem take_take (Γ : Context τ) (m n : Nat) :
    (Γ.take m).take n = Γ.take (min m n) := by
  apply eq_of_toList; simp [take, List.take_take, Nat.min_comm]

@[simp, grind =] theorem drop_drop (Γ : Context τ) (m n : Nat) :
    (Γ.drop m).drop n = Γ.drop (m + n) := by
  apply eq_of_toList; simp [drop, List.drop_drop]

@[simp, grind =] theorem liveIn_take {v : Var} {n : Nat} :
    v.LiveIn (Γ.take n) ↔ v.toNat < n ∧ v.LiveIn Γ := by
  grind [Var.LiveIn]

@[simp, grind =] theorem liveIn_drop {v : Var} {n : Nat} :
    v.LiveIn (Γ.drop n) ↔ (v + n).LiveIn Γ := by
  grind [Var.LiveIn]

@[simp, grind =] theorem take_append_drop (Γ : Context τ) (n : Nat) :
    Γ.drop n ++ Γ.take n = Γ := by
  induction n generalizing Γ
  · grind
  · cases Γ <;> grind

/-! ### staleVars -/

@[simp, grind =] theorem mem_staleVars_iff {v : Var} {Γ : Context τ} :
    v ∈ Γ.staleVars ↔ v.toNat < Γ.size ∧ Γ[v]? = none := by
  suffices Γ.toList[v.toNat]? = some none ↔ v.toNat < Γ.size ∧ ¬Var.LiveIn Γ v by
    simp [staleVars]; grind
  grind [Var.LiveIn, Context.get?]

@[simp, grind =] theorem staleVars_append {Γ Δ : Context τ} :
    (Γ ++ Δ).staleVars = Δ.staleVars ++ (Γ.staleVars.map (fun v : Var => v + Δ.size)) := by
  suffices
    (Γ.toList.zipIdx Δ.toList.length).filterMap (fun x => if x.1.isSome = true then none else some { toNat := x.2 })
    = (Γ.staleVars.map (fun v : Var => v + Δ.size))
  by grind [staleVars]
  rw [List.zipIdx_eq_map_add]
  grind [staleVars]

/-- Erasing a single stale variable does not change the context. -/
@[simp, grind =] theorem eraseVar_staleVars (hv : v ∈ Γ.staleVars) :
    Γ.eraseVar v = Γ := by
  grind

/-- Erasing a subset of stale variable does not change the context. -/
@[simp, grind =] theorem eraseVars_of_subset_staleVars (hvs : vs ⊆ Γ.staleVars) :
    Γ.eraseVars vs = Γ := by
  grind

end Context

/-!
## Decidability
-/

/-- Unrestrictedness of a context is decidable. -/
instance {τ} {Γ : Context τ} : Decidable (Γ.isUnrestricted) :=
  decidable_of_bool (Γ.toList.all (fun t => t.all (·.isUnrestricted))) <| by
    induction Γ <;> grind
