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
variable {τ : Ty}  (v : Var)

section OfList
variable (Γ : List τ.Typ)

@[simp, grind =] theorem getElem?_ofList : (ofList Γ)[v]? = Γ[v.toNat]? := by rfl
@[simp, grind =] theorem getElem_ofList (h) : (ofList Γ)[v]'h = Γ[v.toNat] := by rfl
@[simp, grind =] theorem size_ofList : (ofList Γ).size = Γ.length := by rfl

@[simp] theorem toList_ofList : (ofList Γ).toList = Γ := by rfl
-- FIXME: ^^ This ought to be a grind-lemma, but when tagged grind reports:
--           `invalid pattern, (non-forbidden) application expected #0`

end OfList
section ToList
variable (Γ : Context τ)

@[simp, grind =] theorem ofList_toList : ofList Γ.toList = Γ := by rfl

@[simp, grind =] theorem toList_empty : toList (∅ : Context τ) = [] := by rfl
@[simp, grind =] theorem toList_snoc : toList (Γ <: t) = t :: Γ.toList := by rfl

end ToList
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
## Induction Principles
--------------------------------------------------------------------------------
-/

@[elab_as_elim, induction_eliminator]
def Context.recOn' {motive : Context τ → Sort u}
    (Γ : Context τ)
    (empty : motive ∅)
    (snoc : ∀ Γ t, motive Γ → motive (Γ <: t)) :
    motive Γ :=
  go Γ.toList
where
  go : (Γ : List _) → motive ⟨Γ⟩
  | [] => empty
  | t :: Γ => snoc ⟨Γ⟩ t (go Γ)

@[elab_as_elim, cases_eliminator]
def Context.casesOn' {motive : Context τ → Sort u}
    (Γ : Context τ)
    (empty : motive ∅)
    (snoc : ∀ Γ t, motive (Γ <: t)) :
    motive Γ :=
  recOn' Γ empty (fun Γ t _ => snoc Γ t)

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
theorem eq_of_getElem?_eq {Γ Δ : Context τ} (h : ∀ (v : Var), Γ[v]? = Δ[v]?) :
    Γ = Δ := by
  rcases Γ; rcases Δ
  apply eq_of_toList
  ext v
  grind [h ⟨v⟩]

/-! ### empty -/

@[simp, grind =] theorem getElem?_empty : (∅ : Context τ)[v]? = none := by rfl

/-! ### size -/

@[simp, grind =] theorem size_empty : size (∅ : Context τ) = 0 := rfl
@[simp, grind =] theorem size_snoc : size (Γ <: t) = Γ.size + 1 := rfl

@[grind →]
theorem isSome_getElem?_of_inBounds : v.InBounds Γ → Γ[v]?.isSome := by
  rcases Γ; grind

/-! ### getElem -/

@[simp, grind =] theorem getElem_snoc_zero : (Γ <: t)[Var.ofNat 0]'h = t := rfl
@[simp, grind =] theorem getElem_snoc_succ :
    (Γ <: t)[v + 1]'h = Γ[v]'(by grind) := rfl

@[grind =]
theorem getElem_snoc_eq :
    (Γ <: t)[v]'h =
      if hz : v = Var.ofNat 0 then
        t
      else
        Γ[v - 1]'(by grind) := by
  match v with
  | .ofNat 0 => grind
  | .ofNat (i + 1) => simp; grind

@[simp, typecheck, grind =]
theorem getElem?_snoc_zero : (Γ <: t)[Var.ofNat 0]? = some t := rfl
@[simp, typecheck, grind =]
theorem getElem?_snoc_succ : (Γ <: t)[v + 1]? = Γ[v]? := rfl

/-! ### isUnrestricted -/

@[simp, typecheck, grind .] theorem isUnrestricted_empty : @isUnrestricted τ ∅ := by
  grind [isUnrestricted]

@[simp, typecheck, grind =] theorem isUnrestricted_snoc :
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
  have : (Γ[v]).isUnrestricted = false := by rcases Γ; grind
  grind [isUnrestricted]

theorem isUnrestricted_iff_getElem? (Γ : Context τ) :
    Γ.isUnrestricted ↔ ∀ (v : Var), ∀ t ∈ Γ[v]?, t.isUnrestricted := by
  rcases Γ; grind [isUnrestricted, Var.inBounds_iff_exists]

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

/-! ### eraseVars -/

@[simp, grind =] theorem toList_eraseVars :
  (Γ.eraseVars vs n).toList = Γ.toList.eraseAllIdxP (⟨·⟩ ∈ vs) n := by rfl

@[simp, typecheck, grind =]
theorem eraseVars_nil : Γ.eraseVars [] n = Γ := by simp [eraseVars]

@[simp, typecheck, grind =]
theorem empty_eraseVars : (∅ : Context τ).eraseVars vs n = ∅ := by rfl

@[grind =] theorem snoc_eraseVars :
    (Γ <: t).eraseVars vs n =
      let Γ' := Γ.eraseVars vs (n + 1)
      if ⟨n⟩ ∈ vs then Γ' else Γ' <: t := by
  apply eq_of_toList; grind

@[simp, grind =] theorem snoc_eraseVars_of_mem (h : ⟨n⟩ ∈ vs) :
    (Γ <: t).eraseVars vs n = Γ.eraseVars vs (n + 1) := by grind

@[simp, grind =] theorem snoc_eraseVars_of_notMem (h : ⟨n⟩ ∉ vs) :
    (Γ <: t).eraseVars vs n = Γ.eraseVars vs (n + 1) <: t := by grind

@[grind .]
theorem getElem?_eraseVars_of_getElem? {v : Var} (hΓ : Γ[v]? = some t) (hv : v ∉ vs) :
    ∃ (w : Var), (Γ.eraseVars vs)[w]? = some t :=
  go 0 hΓ hv
where
  go {Γ : Context τ} {v : Var} (n : Nat) (hΓ : Γ[v]? = some t) (hv : v + n ∉ vs) :
      ∃ (w : Var), (Γ.eraseVars vs n)[w]? = some t := by
    induction Γ generalizing v n
    case empty => grind
    case snoc Γ t' ih =>
      cases v
      case zero => use ⟨0⟩; grind
      case succ v =>
        replace hΓ : Γ[v]? = some t := by grind
        obtain ⟨w, ih⟩ := ih (n+1) hΓ <| by
          have : (v + 1 : Var) + n = v + (n + 1) := by ext; grind
          grind
        by_cases ⟨n⟩ ∈ vs
        · use w; grind
        · use w + 1; grind

@[grind .] theorem getElem?_of_getElem?_eraseVars :
    (Γ.eraseVars vs)[v]? = some t → (∃ w ∉ vs, Γ[w]? = some t) := by
  suffices ∀ n,
    (Γ.eraseVars vs n)[v]? = some t → (∃ (w : Var), w + n ∉ vs ∧ Γ[w]? = some t)
  by exact this 0
  intro n hΓ
  induction Γ generalizing v n
  case empty => grind
  case snoc Γ t' ih =>
    have (w : Var) : w + (n + 1) = (w + 1) + n := by grind
    by_cases hn : ⟨n⟩ ∈ vs
    · grind [ih (n + 1)]
    · replace hΓ : (eraseVars vs Γ (n + 1) <: t')[v]? = some t := by grind
      cases v
      · use ⟨0⟩; grind
      · grind [ih (n + 1)]

@[simp] theorem forall_getElem?_eraseVars (P : τ.Typ → Prop) :
    (∀ (v : Var), ∀ t ∈ (Γ.eraseVars vs)[v]?, P t)
    ↔ (∀ (v : Var), ∀ t ∈ Γ[v]?, ¬(v ∈ vs) → P t) := by
  grind [Option.mem_def]

end Context
