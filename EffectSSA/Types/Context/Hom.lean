import EffectSSA.Types.Context.Basic
import EffectSSA.Types.Context.TVar
import EffectSSA.Syntax.Untyped.Substitute

/-!
# Context Homomorphisms
-/
namespace EffectSSA.Context

/--
A context homomorphism `f : Γ.Hom Δ` is map from variables in `Γ` to variables
in `Δ` which preserves the relevant types.

It can be seen as a substitution, or as a computable witness that `Δ` is somehow
"included" in `Γ`.

Note that `Hom` is a structure, but a `CoeFun` instance exists, letting us apply
an `f : Γ.Hom Δ` as if it was a function. See `Hom.apply` for the interpretation
of a context morphism as a function.
-/
structure Hom (Γ Δ : Context τ) where
  /-- The substitution of (raw) variables underlying a context morphism. -/
  applyVar : Var → Var
  /-- `applyVar` preserves types and staleness of variables. -/
  ty_eq : ∀ (v : Var), v.toNat < Γ.size → Γ[v]? = Δ[applyVar v]? := by grind
  /--
  If `v` is in bounds of the domain `Γ`,
  then `applyVar v` is in bounds of the codomain `Δ`.
  -/
  applyVar_lt_size : v.toNat < Γ.size → (applyVar v).toNat < Δ.size := by grind

attribute [grind .] Hom.ty_eq
attribute [grind .] Hom.applyVar_lt_size

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace Hom
variable {τ} {Γ Δ : Context τ}

/--
Applying a context homomorphism `f : Γ.Hom Δ` to a typed variable in `Γ` yields
a variable of the same type in `Δ`.

A `CoeFun` instance exists, such that we can write `f v` to mean `f.apply v`.
-/
def apply (f : Γ.Hom Δ) (v : TVar Γ t) : TVar Δ t where
  toVar := f.applyVar v
instance (Γ Δ : Context τ) : CoeFun (Γ.Hom Δ) (fun _ => ∀ {t}, TVar Γ t → TVar Δ t) where
  coe f := f.apply

/--
Every context homomorphism induces an untyped substitution by forgetting the
type preservation proof.
-/
def asSubstitution (f : Γ.Hom Δ) : Substitution where
  apply := f.applyVar

instance : CoeHead (Γ.Hom Δ) Substitution where
  coe := Hom.asSubstitution

/-! ### Standard Morphisms -/

/-- Identity morphism -/
@[grind] def id (Γ : Context τ) : Γ.Hom Γ where
  applyVar v := v


end Hom

/-!
## Decomposition
--------------------------------------------------------------------------------
-/

/--
A context decomposition `Γ.Decomp Δ₁ Δ₂` is a witness that `Γ = Δ₁ ∘ Δ₂`, in the
form of a pair of context homomorphisms `f₁ : Δ₁.Hom Γ` and `f₂ : Δ₂.Hom Γ`
meaning that (a) every *linear* variable of `Γ` is in the codomain of exactly
one of `f₁` or `f₂` (but not both), and (b) every *unrestricted* variable of `Γ`
is in the codomain of at least one of `f₁` or `f₂` (or both).
-/
structure Decomp (Γ Δ₁ Δ₂ : Context τ) where
  hom₁ : Δ₁.Hom Γ
  hom₂ : Δ₂.Hom Γ
  complete : ∀ {t} (v : TVar Γ t),
    (∃ w, hom₁.apply w = v) ∨ (∃ w, hom₂.apply w = v)
  linear : ∀ t, ¬t.isUnrestricted → ∀ (w₁ w₂ : TVar _ t),
    hom₁.apply w₁ ≠ hom₂.apply w₂

/-!
## Hom Lemmas
--------------------------------------------------------------------------------
-/
namespace Hom
variable {Γ Δ : Context τ} (f : Γ.Hom Δ)

/-! ### asSubstitution / applyVar -/

@[simp, grind =] theorem apply_asSubstitution : f.asSubstitution.apply = f.applyVar := by rfl

/-- Applying the raw substitution to a `TVar Γ` yields a `TVar Δ` -/
@[simp, grind =] theorem applyVar_toVar (v : TVar Γ t) :
    f.applyVar v.toVar = (f.apply v).toVar := by rfl

/-! ### Context.staleVars -/

@[simp, grind =] theorem liveIn_applyVar (hv : v.toNat < Γ.size) :
    (f.applyVar v).LiveIn Δ ↔ v.LiveIn Γ := by
  grind [Var.LiveIn]

/-- Stale variables get mapped to stale variables -/
theorem map_staleVars : Γ.staleVars.map f.applyVar ⊆ Δ.staleVars := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ : ∃ w ∈ Γ.staleVars, v = f.applyVar w := by grind
  grind

/-! ### Context.isUnrestricted -/

/--
If the codomain of a context morphism is unrestricted,
the domain is unrestricted as well.
-/
theorem isUnrestricted_of_isUnrestricted (f : Γ.Hom Δ) :
    Δ.isUnrestricted → Γ.isUnrestricted := by
  intro hΔ v t hv
  apply hΔ (f.applyVar v)
  grind
