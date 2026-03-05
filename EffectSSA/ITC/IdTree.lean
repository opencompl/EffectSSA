

/-!
# Id Trees
These formalize the id component of an Interval Tree Clock.

[1]: Almeida et al. "Interval Tree Clocks: A Logical Clock for Dynamic Systems"
-/
namespace EffectSSA.ITC

/--
An `IdTree` represents a subset of the interval `[0, 1]` as a binary tree with
Booleans at the leaves.
-/
inductive IdTree
  | zero
  | one
  | node (left : IdTree) (right : IdTree)
  deriving DecidableEq

/-!
## Normal Forms
Section 5.2 of [1]
-/
namespace IdTree

def normalize : IdTree → IdTree
  | zero => zero
  | one => one
  | node left right =>
    match left.normalize, right.normalize with
    | zero, zero => zero
    | one, one => one
    | left, right => node left right

/-!
## Lemmas
-/
section Lemmas
variable {l r : IdTree}

@[simp, grind =] theorem normalize_zero : normalize zero = zero := by rfl
@[simp, grind =] theorem normalize_one : normalize one = one := by rfl

@[simp, grind =] theorem normalize_normalize (i : IdTree) : (normalize i).normalize = normalize i := by
  induction i <;> grind [normalize]

@[simp, grind =] theorem normalize_node_eq_zero_iff :
    normalize (node l r) = zero ↔ l.normalize = zero ∧ r.normalize = zero := by
  grind [normalize]

@[simp, grind =] theorem normalize_node_eq_one_iff :
    normalize (node l r) = one ↔ l.normalize = one ∧ r.normalize = one := by
  grind [normalize]

/-!
We'll often use an assumption of the form `i.normalize = i` to express that `i`
is canonical. Although we don't introduce an explicit Lean definition, we do
use the name *canonical* to refer to such assumption in theorems.
-/


@[simp, grind =] theorem node_canonical_iff :
    normalize (node l r) = node l' r'
    ↔ l.normalize = l' ∧ r.normalize = r'
      ∧ ¬(l' = zero ∧ r' = zero) ∧ ¬(l' = one ∧ r' = one) := by
  grind [normalize]

@[simp, grind =] theorem zero_node_canonical_iff :
    normalize (node zero r) = node zero r' ↔ r.normalize = r' ∧ r' ≠ zero := by grind

@[simp, grind =] theorem node_zero_canonical_iff :
    normalize (node l zero) = node l' zero ↔ l.normalize = l' ∧ l' ≠ zero := by grind


-- theorem canonical_node_iff : (node l r).normalize = (node l r)

end Lemmas
