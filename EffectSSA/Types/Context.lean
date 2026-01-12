import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Syntax.Basic
import EffectSSA.Types.Basic

import Mathlib.Data.Vector.Defs
import Mathlib.Data.Fintype.Basic

/-!
# Typing Context
-/
namespace EffectSSA

/-!
## Types
--------------------------------------------------------------------------------
-/

/--
A `Context τ n` is a mapping from `n` variables to their types.
-/
structure Context (τ : Ty) n where
  vec : List.Vector τ.Typ n

/-!
## Definitions
--------------------------------------------------------------------------------
-/

namespace Context

/--
We write `Γ[v]` to indicate the type that context `Γ` assigned to variable `v`.
-/
instance : GetElem (Context τ n) (Var n) (τ.Typ) (fun _ _ => True) where
  getElem Γ v _ := Γ.vec[v.val]

/--
`Γ <: t` is the context `Γ` expanded with a new variable of type `t`.
-/
def snoc (Γ : Context τ n) (t : τ.Typ) : Context τ (n + 1) :=
  ⟨Γ.vec.cons t⟩
@[inherit_doc] infixl:67 " <: " => snoc

/--
A context is unrestricted if *all* contained types are unrestricted.
-/
def isUnrestricted (Γ : Context τ n) : Prop :=
  ∀ (v : Var n), Γ[v].isUnrestricted

/--
Unrestrictedness of a context is decidable.
-/
instance {Γ : Context τ n} : Decidable (isUnrestricted Γ) := by
  unfold isUnrestricted Var; infer_instance

/-! ### vars -/

/--
`Γ.eraseVar v` removes variable `v` from the context.
-/
def eraseVar (v : Var n) (Γ : Context τ n) : Context τ (n - 1) :=
  ⟨Γ.vec.eraseIdx v.toFin⟩

end Context

/-!
## Lemmas
--------------------------------------------------------------------------------
-/
