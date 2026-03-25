import EffectSSA.Types.Context.Basic
import EffectSSA.Types.Context.Lemmas

/-!
# Intrinsically Well-typed Variables
-/
namespace EffectSSA
variable {τ}

/--
`TVar Γ t` is a variable which is guaranteed to be assigned
type `t` in context `Γ`.
-/
structure TVar (Γ : Context τ) (t : τ.Typ) where
  ofVar ::
    toVar : Var
    wt : Γ[toVar]? = some t := by grind

/-!
## Coercions
--------------------------------------------------------------------------------
The typed structures can be implicitly coerced into the underlying
untyped variants
-/
variable {Γ : Context τ}

instance : CoeOut (TVar Γ t) Var where coe := TVar.toVar

/-!
## Grind Attributes
--------------------------------------------------------------------------------
-/

grind_pattern TVar.wt => TVar.toVar self

/-!
## Definitions
-/

namespace TVar

/-- Get the index of a (typed) variable. -/
abbrev toNat (v : TVar Γ t) : Nat := v.toVar.toNat

/-- The index of a typed variable is in bounds of the context is typed with. -/
@[simp] theorem toNat_lt (v : TVar Γ t) : v.toNat < Γ.size := by
  grind
grind_pattern TVar.toNat_lt => v.toNat
