
/-!
# List

This file defines `List.eraseIdxP`, a function to erase multiple elements from
a list based on a predicate on indices.

TODO: we could perhaps upstream this?
-/
namespace List

/--
Remove the element at *all* indices `i` for which `p` returns `true`,
optionally starting from an index other than `0`.
If no index satisfies `p`, then the list is returned unchanged.
-/
def eraseAllIdxP (p : Nat → Bool) (xs : List α) (n := 0) : List α :=
  (xs.zipIdx n).filterMap fun xi =>
    if p xi.2 then
      none
    else
      some xi.1

/-!
## Lemmas
-/

@[simp, grind =] theorem eraseAllIdxP_nil : eraseAllIdxP p ([] : List α) = [] := by rfl

@[simp, grind =] theorem eraseAllIdxP_cons {x : α} {xs : List α} :
    eraseAllIdxP p (x :: xs) n =
      let xs' := xs.eraseAllIdxP p (n + 1)
      if p n then xs' else x :: xs' := by
  simp [eraseAllIdxP]; grind
