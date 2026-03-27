import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Syntax.Untyped.Basic
import EffectSSA.Types.Basic

import EffectSSA.Types.Context.ListErase

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
A `Context τ` is a mapping from variables to (optional) types.

A linear variable, when used, will be replaced by a `none` to indicate that the
corresponding variable is no longer available. By keeping the entry in the
context, we prevent having to reuse variable indices.

As is conventional, contexts grow towards the right, written as `Γ <: t`.
Additionally, indexing happens from right-to-left, such that the `t` in `Γ <: t`
is actually index `0`. Hence, we model a context as a regular List internally.
-/
structure Context (τ : Ty) where
  ofList :: toList : List (Option τ.Typ)

/-!
## Definitions
--------------------------------------------------------------------------------
-/

@[grind =]
abbrev Context.size (Γ : Context τ) : Nat := Γ.toList.length

/--
`Γ.get? v` returns the type assigned to variable `v`,
returning `none` when `v` is either out of bounds for `Γ`,
or when `v` is "stale", meaning that the corresponding entry in `Γ` is `none`.

The preferred spelling of `Γ.get? v` is `Γ[v]?`.
-/
protected def Context.get? (Γ : Context τ) (v : Var) : Option τ.Typ :=
  Γ.toList[v.toNat]?.join

/--
`v.LiveIn Γ` holds when the index of variable `v` is in bounds of context `Γ`,
and is _live_, i.e., has a type assigned to it in `Γ`.
-/
def Var.LiveIn (Γ : Context τ) (v : Var) : Prop :=
  (Γ.get? v).isSome

namespace Context

/-- `Γ[v]?` is an alias for `Γ.get? v` -/
instance : GetElem? (Context τ) (Var) τ.Typ (fun Γ v => v.LiveIn Γ) where
  getElem Γ v h := (Γ.get? v).get h
  getElem? Γ v  := Γ.get? v

/--
`∅` is the empty context.
-/
instance : EmptyCollection (Context τ) where emptyCollection := ⟨[]⟩

/--
`Γ <: t` expands the context `Γ` with a new (live) variable of type `t`.

The new variable will have index `0`.
-/
def snoc (Γ : Context τ) (t : τ.Typ) : Context τ :=
  ⟨Γ.toList.cons (some t)⟩
@[inherit_doc] infixl:67 " <: " => snoc

/--
`Γ.snocStale` expands the context `Γ` with a new stale variable.

This should probably not be used by users of the API; instead, it should only
show up in the intermediate state of a proof.
-/
def snocStale (Γ : Context τ) : Context τ :=
  ⟨Γ.toList.cons none⟩

/--
A context is unrestricted if *all* contained types are unrestricted.
-/
def isUnrestricted (Γ : Context τ) : Prop :=
  ∀ (v : Var) {t}, Γ[v]? = some t → t.isUnrestricted

/-! ### vars -/

/--
`Γ.set v t` sets variable `v` to `t`, or
returns `Γ` unchanged if `v` is not in bounds of `Γ`.
-/
def set (Γ : Context τ) (v : Var) (t? : Option τ.Typ) : Context τ :=
  ⟨Γ.toList.set v.toNat t?⟩

/--
`Γ.eraseVar v` marks variable `v` as stale, or returns `Γ` unchanged if `v` is
not in bounds of `Γ`.
-/
def eraseVar (v : Var) (Γ : Context τ) : Context τ :=
  ⟨Γ.toList.set v.toNat none⟩

/--
`Γ.eraseVars vs` marks a list of variables `vs` as stale,
optionally starting the first variable at an index other than 0.

For example:
* `[α, β, γ].eraseVars [0, 2] = [β]`
* `[α, β, γ].eraseVars [0]    = [β, γ]`
* `[α, β, γ].eraseVars [0] 1  = [α, γ]`
-/
def eraseVars (vs : List Var) (Γ : Context τ) (n : Nat := 0) : Context τ :=
  let f := fun v Γ => Γ.eraseVar (v + n)
  vs.foldr f Γ

/-- `Γ.staleVars` returns the list of variables in `Γ` which are stale. -/
def staleVars (Γ : Context τ) : List Var :=
  Γ.toList.zipIdx.filterMap fun (t?, i) =>
    if t?.isSome then none else some (Var.ofNat i)

/-! ### drop / take -/

/-- Removes the first (i.e, right-most) `n` types of the context `Γ`. -/
def drop (Γ : Context τ) (n : Nat) : Context τ :=
  ⟨Γ.toList.drop n⟩

/-- Extracts the first (i.e, right-most) `n` types of the context `Γ`. -/
def take (Γ : Context τ) (n : Nat) : Context τ :=
  ⟨Γ.toList.take n⟩

/-! ### append -/

instance : Append (Context τ) where
  append Γ Δ := ⟨Δ.toList ++ Γ.toList⟩
  -- ^^ Recall that contexts grow towards the right,
  --    but are internally implemented as lists that grow towards the left.
  --    Hence, we invert the arguments here.

end Context
