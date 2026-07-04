module

public import ITree.Definition
public import ITreeExtras.Basic

/-!
# `ITree.interp'`: interpretation with an extra `tau` at each visible step

`ITree.interp'` is a variant of `ITree.interp` that emits an extra `tau` after
handling each visible effect. This makes it satisfy `interp'_vis`
(the analogue of `interp_vis_with_tau`), at the cost of an extra step of
computation per visible node.
-/

@[expose] public section
namespace ITree

/-- Notation for effect handlers targeting a monad `m`. -/
abbrev Effect.Transform (ε : Effect) (m : Type _ → Type _) :=
  (i : ε.I) → m (ε.O i)
@[inherit_doc] scoped infixl:50 unicode(" ⤳ ", " ~> ") => ITree.Effect.Transform

namespace ITree

variable {E F : Effect.{u}} {R : Type u}

/--
`interp'` is a variant of `ITree.interp` that inserts a `tau` after handling
each visible effect.

Counterintuitively, this extra tau makes it *easier* to prove certain properties.
-/
def interp' (f : E ⤳ ITree F) : ITree E R → ITree F R :=
  iter fun t =>
    match t.unfold with
    | .ret r   => return (.inr r)
    | .tau t   => tau (return (.inl t))
    | .vis i k => do
      let o ← f i
      tau (return (.inl (k o)))

variable (f : E ⤳ ITree F)

@[simp, grind =] theorem interp'_ret (r : R) :
    interp' f (ret r) = ret r := by
  unfold interp' iter
  simp

@[simp, grind =] theorem interp'_pure (r : R) :
    interp' f (pure r) = pure r := by
  simp

@[simp, grind =] theorem interp'_tau (t : ITree E R) :
    interp' f (tau t) = tau (interp' f t) := by
  unfold interp'
  rw (occs := [1]) [iter]
  simp

@[simp] theorem interp'_vis (i : E.I) (k : E.O i → ITree E R) :
    interp' f (vis i k)
    = f i >>= fun o => (tau <| interp' f (k o)) := by
  unfold interp'
  rw (occs := [1]) [iter]
  simp
