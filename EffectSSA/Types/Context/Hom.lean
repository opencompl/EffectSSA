import EffectSSA.Types.Context.Basic
import EffectSSA.Types.Context.TVar

/-!
# Context Homomorphisms
-/
namespace EffectSSA.Context

/--
A context homomorphism `f : Γ.Hom Δ` is map from variables in `Γ` to variables
in `Δ` which preserves the relevant types.

It can be seen as a substitution, or as a computable witness that `Δ` is somehow
"included" in `Γ`.
-/
structure Hom (Γ Δ : Context τ) where
  raw : Var → Var
  ty_eq : ∀ (v : Var), ∀ t ∈ Γ[v]?, Δ[raw v]? = some t

attribute [grind .] Hom.ty_eq

/--
Applying a context homomorphism `f : Γ.Hom Δ` to a typed variable in `Γ` yields
a variable of the same type in `Δ`.
-/
def Hom.apply (f : Γ.Hom Δ) (v : TVar Γ t) : TVar Δ t where
  toVar := f.raw v

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
