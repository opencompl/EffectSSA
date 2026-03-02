
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

@[grind =] theorem eraseAllIdxP_cons {x : α} {xs : List α} :
    eraseAllIdxP p (x :: xs) n =
      let xs' := xs.eraseAllIdxP p (n + 1)
      if p n then xs' else x :: xs' := by
  simp [eraseAllIdxP]; grind

/-- If `p` returns false on all inputs, `eraseAllIdxP p` has no effect. -/
@[simp, grind =] theorem eraseAllIdxP_of_false {xs : List α}
    (h : ∀ i < xs.length, p (i + n) = false) :
    xs.eraseAllIdxP p n = xs := by
  simp [eraseAllIdxP]
  induction xs generalizing n
  case nil => rfl
  case cons _x xs ih =>
    have : p n = false := by grind [h 0]
    have h' (i : Nat) : i < xs.length → p (i + (n + 1)) = false := by grind [h (i + 1)]
    simp; grind
