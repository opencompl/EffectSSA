/-!
# Event Trees
These formalize the event component of an Interval Tree Clock.

An event tree is a representation of function `f: [0,1] → ℕ`, where the value
represents the number of events that have occurred in that portion of the
interval.

[1]: Almeida et al. "Interval Tree Clocks: A Logical Clock for Dynamic Systems"
-/
namespace EffectSSA.ITC

/--
An `EventTree` represents a function `f: [0,1] → ℕ` as a binary tree with
natural numbers at the leaves and nodes.

- `leaf n` represents the constant function `f(x) = n`
- `node n l r` represents a function where `n` is a base value added to the
  entire interval, and `l`/`r` are the left/right subtrees for `[0,0.5)` and
  `[0.5,1]` respectively.
-/
inductive EventTree
  | leaf (n : Nat)
  | node (n : Nat) (left : EventTree) (right : EventTree)
  deriving DecidableEq, Repr

/-!
## Normal Forms
Section 5.2 of [1]

The normal form ensures that in a node `(n, l, r)`, the minimum of the
values at the roots of `l` and `r` is zero. This is achieved by "lifting"
the minimum into `n`.
-/
namespace EventTree

/-- Get the value at the root of an event tree. -/
def rootValue : EventTree → Nat
  | leaf n => n
  | node n _ _ => n

/-- Lift a value `k` into the root of an event tree. -/
def lift (k : Nat) : EventTree → EventTree
  | leaf n => leaf (n + k)
  | node n l r => node (n + k) l r

/-- Lower the root value by `k`, assuming `k ≤ rootValue e`. -/
def lower (k : Nat) : EventTree → EventTree
  | leaf n => leaf (n - k)
  | node n l r => node (n - k) l r

/--
Normalize an event tree to its canonical form.

The key invariant is that in a normalized `node n l r`, the minimum of
`l.rootValue` and `r.rootValue` is zero.
-/
def normalize : EventTree → EventTree
  | leaf n => leaf n
  | node n l r =>
    let l' := l.normalize
    let r' := r.normalize
    let minVal := min l'.rootValue r'.rootValue
    if minVal = 0 then
      node n l' r'
    else
      -- Lift the minimum into n, lower it from l' and r'
      node (n + minVal) (l'.lower minVal) (r'.lower minVal)

/-!
## Lemmas
-/
section Lemmas
variable {e : EventTree} {l r : EventTree} {n m k : Nat}

@[simp] theorem rootValue_leaf : (leaf n).rootValue = n := rfl
@[simp] theorem rootValue_node : (node n l r).rootValue = n := rfl

@[simp] theorem lift_leaf : (leaf n).lift k = leaf (n + k) := rfl
@[simp] theorem lift_node : (node n l r).lift k = node (n + k) l r := rfl

@[simp] theorem lower_leaf : (leaf n).lower k = leaf (n - k) := rfl
@[simp] theorem lower_node : (node n l r).lower k = node (n - k) l r := rfl

@[simp] theorem rootValue_lift : (e.lift k).rootValue = e.rootValue + k := by
  cases e <;> rfl

@[simp] theorem rootValue_lower : (e.lower k).rootValue = e.rootValue - k := by
  cases e <;> rfl

@[simp] theorem lift_zero : e.lift 0 = e := by
  cases e <;> simp [lift]

@[simp] theorem lower_zero : e.lower 0 = e := by
  cases e <;> simp [lower]

@[simp] theorem lift_lift : (e.lift k).lift m = e.lift (k + m) := by
  cases e <;> simp [lift, Nat.add_assoc]

@[simp] theorem normalize_leaf : (leaf n).normalize = leaf n := rfl

theorem normalize_node_eq :
    (node n l r).normalize =
    let l' := l.normalize
    let r' := r.normalize
    let minVal := min l'.rootValue r'.rootValue
    if minVal = 0 then node n l' r'
    else node (n + minVal) (l'.lower minVal) (r'.lower minVal) := rfl

/-- A normalized node has minimum child root value equal to zero. -/
theorem normalize_node_min_rootValue :
    ∀ e : EventTree, ∀ n l r, e.normalize = node n l r →
      min l.rootValue r.rootValue = 0 := by
  intro e
  induction e with
  | leaf _ => intro _ _ _ h; simp [normalize] at h
  | node m el er ihl ihr =>
    intro n l r h
    simp only [normalize] at h
    split at h
    · case isTrue hmin =>
      injection h with hn hl hr
      simp [← hl, ← hr, hmin]
    · case isFalse hmin =>
      injection h with hn hl hr
      simp [← hl, ← hr, rootValue_lower]
      omega

@[simp] theorem normalize_normalize : (e.normalize).normalize = e.normalize := by
  induction e with
  | leaf n => rfl
  | node n l r ihl ihr =>
    simp only [normalize]
    split
    · case isTrue h =>
      simp only [normalize, ihl, ihr]
      split <;> rfl
    · case isFalse h =>
      sorry

end Lemmas

/-!
## Comparison (≤)
-/
section Comparison

/-- The depth of an event tree. -/
def depth : EventTree → Nat
  | leaf _ => 0
  | node _ l r => 1 + max l.depth r.depth

/--
Event tree ordering: `e₁ ≤ e₂` means that at every point in `[0,1]`,
the value of `e₁` is at most the value of `e₂`.
-/
def le : EventTree → EventTree → Bool
  | leaf n₁, leaf n₂ => n₁ ≤ n₂
  | leaf n₁, node n₂ l₂ r₂ => n₁ ≤ n₂ ∧ le (leaf 0) l₂ ∧ le (leaf 0) r₂
  | node n₁ l₁ r₁, leaf n₂ => n₁ ≤ n₂ ∧ le l₁ (leaf (n₂ - n₁)) ∧ le r₁ (leaf (n₂ - n₁))
  | node n₁ l₁ r₁, node n₂ l₂ r₂ =>
    if n₁ ≤ n₂ then
      le l₁ (l₂.lift (n₂ - n₁)) ∧ le r₁ (r₂.lift (n₂ - n₁))
    else
      le (l₁.lift (n₁ - n₂)) l₂ ∧ le (r₁.lift (n₁ - n₂)) r₂
termination_by e₁ e₂ => e₁.depth + e₂.depth
decreasing_by all_goals sorry

instance : LE EventTree := ⟨fun e₁ e₂ => le e₁ e₂⟩

instance : DecidableRel (α := EventTree) (· ≤ ·) := fun e₁ e₂ =>
  if h : le e₁ e₂ then isTrue h else isFalse h

end Comparison

/-!
## Join (⊔)
-/
section Join

/--
Join of two event trees: returns the pointwise maximum.
-/
def join : EventTree → EventTree → EventTree
  | leaf n₁, leaf n₂ => leaf (max n₁ n₂)
  | leaf n₁, node n₂ l₂ r₂ =>
    if n₁ ≤ n₂ then node n₂ l₂ r₂
    else node n₁ (join (leaf 0) (l₂.lift (n₂ - n₁))) (join (leaf 0) (r₂.lift (n₂ - n₁)))
  | node n₁ l₁ r₁, leaf n₂ =>
    if n₂ ≤ n₁ then node n₁ l₁ r₁
    else node n₂ (join (l₁.lift (n₁ - n₂)) (leaf 0)) (join (r₁.lift (n₁ - n₂)) (leaf 0))
  | node n₁ l₁ r₁, node n₂ l₂ r₂ =>
    if n₁ ≤ n₂ then
      node n₂ (join (l₁.lift (n₂ - n₁)) l₂) (join (r₁.lift (n₂ - n₁)) r₂)
    else
      node n₁ (join l₁ (l₂.lift (n₁ - n₂))) (join r₁ (r₂.lift (n₁ - n₂)))
termination_by e₁ e₂ => e₁.depth + e₂.depth
decreasing_by all_goals sorry

instance : Max EventTree := ⟨join⟩

end Join

end EventTree
end EffectSSA.ITC
