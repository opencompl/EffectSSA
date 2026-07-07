module

public import ITreeExtras.Definition

/-!
# ITree `iter'` combinator

This file defines `iter'`, which is morally equivalent to `iter`,
except that it inserts an extra `tau` in the recursive case,
making it easier to prove properties about.
-/

@[expose] public section
namespace ITree.ITree
variable {ε} {κ} [Effect.{u} ε κ] {α : Type _}

def iter' {α β} (t : α → ITree ε (α ⊕ β)) (a : α) : ITree ε β :=
  (t a) >>= recurse t
partial_fixpoint
where @[grind] recurse (t : α → ITree ε (α ⊕ β)) : α ⊕ β → ITree ε β
  | .inl a => tau <| .iter' t a
  | .inr b => return b
  partial_fixpoint

@[simp, grind =] theorem iter'.recurse_inl :
    recurse t (.inl a) = (tau <| .iter' t a) := by
  rw [recurse]

@[simp, grind =] theorem iter'.recurse_inr :
    recurse t (.inr b) = return b := by
  rw [recurse]
