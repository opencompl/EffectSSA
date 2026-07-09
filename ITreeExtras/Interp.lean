module

public import ITreeExtras.Definition
public import ITreeExtras.Basic

/-!
# `ITree.interp'`: interpretation with an extra `tau` at each visible step

This file defines `ITree.interp'` as a variant of `ITree.interp` that emits an
extra `tau` after handling each visible effect.
-/

@[expose] public section
namespace ITree

/-- Notation for effect handlers targeting a monad `m`. -/
abbrev Effect.Transform (ε) {κ} [Effect ε κ] (m : Type u → Type u) :=
  (i : ε) → m (κ i)
@[inherit_doc] scoped infixr:25 unicode(" ⤳ ", " ~> ") => ITree.Effect.Transform

namespace ITree

variable {ε} {κε} [Effect.{u} ε κε]
         {δ} {κδ} [Effect.{u} δ κδ]
         {α}

/--
`interp'` is a variant of `ITree.interp` that inserts a `tau` after handling
each visible effect.

Counterintuitively, this extra tau makes it *easier* to prove certain properties.
-/
def interp' (f : ε ⤳ ITree δ) : ITree ε α → ITree δ α :=
  iter fun t =>
    match t.unfold with
    | .ret r   => return (.inr r)
    | .tau t   => tau (return (.inl t))
    | .vis i k => do
      let o ← f i
      tau (return (.inl (k o)))

section InterpLemmas

variable (f : ε ⤳ ITree δ)

@[simp, grind =] theorem interp'_ret (r : α) :
    interp' f (ret r) = ret r := by
  unfold interp' iter
  simp

@[simp, grind =] theorem interp'_pure (r : α) :
    interp' f (pure r) = pure r := by
  simp

@[simp, grind =] theorem interp'_tau (t : ITree ε α) :
    interp' f (tau t) = tau (interp' f t) := by
  unfold interp'
  rw (occs := [1]) [iter]
  simp

@[simp] theorem interp'_vis (i : ε) (k : κε i → ITree ε α) :
    interp' f (vis i k)
    = f i >>= fun o => (tau <| interp' f (k o)) := by
  unfold interp'
  rw (occs := [1]) [iter]
  simp

end InterpLemmas

/-! ### Interpreting Sum Effects -/

/--
Given an ITree with events in `ε ⊕ δ`,
interpret only events in `ε` using the handler `f`,
leaving events in `δ` as-is.
-/
def interpLeft (f : ε ⤳ ITree δ) : ITree (ε ⊕ δ) α → ITree δ α :=
  interp' (Sum.casesOn · f (Effect.trigger δ))
