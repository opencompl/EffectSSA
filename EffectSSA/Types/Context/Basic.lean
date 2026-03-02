import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Syntax.Untyped.Basic
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
A `Context τ` is a mapping from `n` variables to their types.
-/
structure Context (τ : Ty) where
  ofList :: toList : List τ.Typ

/-!
## Definitions
--------------------------------------------------------------------------------
-/

@[grind =]
abbrev Context.size (Γ : Context τ) : Nat := Γ.toList.length

def Var.InBounds (Γ : Context τ) (v : Var) : Prop := v.toNat < Γ.size

namespace Context

/--
We write `Γ[v]` to indicate the type that context `Γ` assigned to variable `v`.
-/
instance : GetElem? (Context τ) (Var) (τ.Typ) (fun Γ v => v.InBounds Γ) where
  getElem Γ v _ := Γ.toList[v.toNat]
  getElem? Γ v := Γ.toList[v.toNat]?

/--
`∅` is the empty context.
-/
instance : EmptyCollection (Context τ) where emptyCollection := ⟨[]⟩

/--
`Γ <: t` is the context `Γ` expanded with a new variable of type `t`.
-/
def snoc (Γ : Context τ) (t : τ.Typ) : Context τ :=
  ⟨Γ.toList.cons t⟩
@[inherit_doc] infixl:67 " <: " => snoc

/--
A context is unrestricted if *all* contained types are unrestricted.
-/
def isUnrestricted (Γ : Context τ) : Prop :=
  ∀ (v : Var), (h : v.InBounds Γ) → Γ[v].isUnrestricted

/--
Unrestrictedness of a context is decidable.
-/
instance {Γ : Context τ} : Decidable (isUnrestricted Γ) :=
  decidable_of_iff (
      List.range Γ.size |>.attach |>.all fun ⟨x, hx⟩ =>
        let v := Var.ofNat x
        have : v.InBounds Γ := by simpa using hx
        Γ[v].isUnrestricted
      ) <| by
    simp [isUnrestricted, Var.InBounds]
    grind


/-! ### vars -/

/--
`Γ.eraseVar v` removes variable `v` from the context.
-/
def eraseVar (v : Var) (Γ : Context τ) : Context τ :=
  ⟨Γ.toList.eraseIdx v.toNat⟩

/--
`Γ.eraseVars vs` removes a list of variables `vs` from the context.
-/
def eraseVars (vs : List Var) (Γ : Context τ) : Context τ :=
  vs.foldr eraseVar Γ

end Context
