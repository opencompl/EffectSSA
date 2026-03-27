import EffectSSA.Types.Context.Basic
import EffectSSA.Types.Context.Hom
import EffectSSA.Types.Context.Lemmas

/-!
# `Context.IsDerivedFrom`
-/
namespace EffectSSA.Context

/--
`Δ.IsDerivedFrom Γ` holds when `Δ` can be obtained from `Γ` by:
1. optionally erasing (making stale) some variables from `Γ`, and
2. prepending zero or more fresh variables.

This captures the relationship between an input context `Γ` and
output context `Δ` of a well-typed sequence of instructions.
-/
@[grind, grind cases]
structure IsDerivedFrom (Δ Γ : Context τ) : Prop where
  /-- The output context has at least as many variables as the input. -/
  size_le : Γ.size ≤ Δ.size
  /-- Any type still present at an old position must agree with `Γ`. -/
  eq_some : ∀ (v : Var), v.toNat < Γ.size →
      ∀ t, Δ[v + (Δ.size - Γ.size)]? = some t → Γ[v]? = some t
  /-- Stale positions in `Γ` remain stale in `Δ`. -/
  eq_none : ∀ (v : Var), v.toNat < Γ.size →
      Γ[v]? = none → Δ[v + (Δ.size - Γ.size)]? = none

/-!
## replaceSuffix
--------------------------------------------------------------------------------
-/

/--
Suppose that context `Δ` is derived from some `Γ`,
construct a context which is analogous,
but derived from another context `Γ'` instead,
by mapping the part of `Δ` that derives from `Γ` along
a context morphism `f : Γ.Hom Γ'`

Note that this definition likely only makes sense when `Δ.IsDerivedFrom Γ`,
but this is not required for the definition to apply.
-/
def replaceSuffix (Δ : Context τ) {Γ Γ' : Context τ} (f : Γ.Hom Γ') : Context τ :=
  let n := Δ.size - Γ.size
  let us := (Δ.drop n).staleVars.map f.applyVar
  (Γ'.eraseVars us) ++ (Δ.take n)

/-!
## IsDerivedFrom Lemmas
--------------------------------------------------------------------------------
-/
section IsDerivedFrom
variable {Γ Δ : Context τ}

attribute [grind =] Nat.add_sub_cancel_left

/-! ### `snoc` -/

/-- Adding a fresh variable keeps old variables untouched. -/
theorem isDerivedFrom_snoc_self (Γ : Context τ) (t : τ.Typ) : (Γ <: t).IsDerivedFrom Γ := by grind

/-! ### `snocStale` -/

theorem isDerivedFrom_snocStale_self (Γ : Context τ) : Γ.snocStale.IsDerivedFrom Γ := by grind

/-! ### eraseVar -/

/-- Erasing a variable produces a valid derived context. -/
theorem isDerivedFrom_eraseVar (Γ : Context τ) (v : Var) : (Γ.eraseVar v).IsDerivedFrom Γ where
  size_le := by grind
  eq_some := by simp; grind
  eq_none := by simp; grind


/-- Erasing multuple variables produces a valid derived context. -/
theorem isDerivedFrom_eraseVars : (Γ.eraseVars v).IsDerivedFrom Γ where
  size_le := by grind
  eq_some := by simp
  eq_none := by simp; grind

/-! ### Reflexivity & Transitivity -/

theorem isDerivedFrom_refl (Γ : Context τ) : Γ.IsDerivedFrom Γ where
  size_le := le_refl _
  eq_some := by grind
  eq_none := by grind

/-- `IsDerivedFrom` is transitive. -/
theorem isDerivedFrom_trans {Ξ Δ Γ : Context τ}
    (h₂ : Ξ.IsDerivedFrom Δ) (h₁ : Δ.IsDerivedFrom Γ) : Ξ.IsDerivedFrom Γ := by
  have (v : Var) : v + (Δ.size - Γ.size) + (Ξ.size - Δ.size) = v + (Ξ.size - Γ.size) := by
    ext; grind
  grind

/-! ### characterization of IsDerived-/

@[grind →] theorem IsDerivedFrom.eq_eraseVars_append (h : Δ.IsDerivedFrom Γ) :
    let n := Δ.size - Γ.size
    Δ = Γ.eraseVars ((Δ.drop n).staleVars) ++ (Δ.take n) := by
  intro n
  suffices Δ.drop n = Γ.eraseVars ((Δ.drop n).staleVars) by grind
  grind

@[grind =] theorem eq_eraseVars_append_iff_isDerived :
    Δ.IsDerivedFrom Γ
    ↔ let n := Δ.size - Γ.size
      Δ = Γ.eraseVars ((Δ.drop n).staleVars) ++ (Δ.take n) := by
  grind

@[grind =] theorem isDerivedFrom_snocStale_iff (h : Δ.size ≥ Γ.size) :
    Δ.snocStale.IsDerivedFrom Γ ↔ Δ.IsDerivedFrom Γ := by
  have : Δ.size + 1 - Γ.size = (Δ.size - Γ.size) + 1 := by grind
  simp [eq_eraseVars_append_iff_isDerived]
  grind

@[grind =] theorem isDerivedFrom_snoc_iff {h : Δ.size ≥ Γ.size} :
    (Δ <: t).IsDerivedFrom Γ ↔ Δ.IsDerivedFrom Γ := by
  have : Δ.size + 1 - Γ.size = (Δ.size - Γ.size) + 1 := by grind
  simp [eq_eraseVars_append_iff_isDerived]
  grind

-- TODO: isDerivedFrom_eraseVars_{left,right}_iff

end IsDerivedFrom

/-!
## `replaceSuffix` Lemmas
--------------------------------------------------------------------------------
-/
section ReplaceSuffix
variable {Δ Γ Γ' : Context τ} {f : Γ.Hom Γ'}

/-! ### snoc -/

@[simp, grind =] theorem replaceSuffix_snoc_of_le_size (h : Γ.size ≤ Δ.size) :
    (Δ <: t).replaceSuffix f = (Δ.replaceSuffix f) <: t := by
  have : Δ.size + 1 - Γ.size = Δ.size - Γ.size + 1 := by grind
  grind [replaceSuffix]

@[simp, grind =] theorem replaceSuffix_snocStale_of_le_size (h : Γ.size ≤ Δ.size) :
    (Δ.snocStale).replaceSuffix f = (Δ.replaceSuffix f).snocStale := by
  -- TODO: this theorem can likely be generalized by dropping the `h` assumption
  have : Δ.size + 1 - Γ.size = Δ.size - Γ.size + 1 := by grind
  grind [replaceSuffix]

@[simp, grind =] theorem replaceSuffix_append_of_le_size {Δ₁ Δ₂ : Context τ}
    (h : Γ.size ≤ Δ₁.size) :
    (Δ₁ ++ Δ₂).replaceSuffix f = (Δ₁.replaceSuffix f) ++ Δ₂ := by
  induction Δ₂ <;> grind

/-! ### id -/

/-- `Γ.replaceSuffix f`, where `Γ` is the domain of `f`, is the codomain of `f`. -/
@[simp, grind =] theorem replaceSuffix_self (f : Γ.Hom Γ') : Γ.replaceSuffix f = Γ' := by
  grind [replaceSuffix]

@[simp, grind =] theorem replaceSuffix_id (h : Δ.IsDerivedFrom Γ) : Δ.replaceSuffix (Hom.id Γ) = Δ := by
  simp [replaceSuffix, Hom.id]
  grind

end ReplaceSuffix
