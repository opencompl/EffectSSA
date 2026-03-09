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
-/
inductive EventTree
  /-- `leaf n` represents the constant function `f(x) = n` -/
  | leaf (n : Nat)
  /--
  `node n l r` represents a function where `n` is a base value added to the
  entire interval, and `l`/`r` are the left/right subtrees for `[0,0.5)` and
  `[0.5,1]` respectively.
  -/
  | node (n : Nat) (left : EventTree) (right : EventTree)
  deriving DecidableEq, Repr

/-!
## Basic Definitions
-/
namespace EventTree
section Defs

/-- Return the value at the root of an event tree. -/
def rootValue : EventTree → Nat
  | leaf n => n
  | node n _ _ => n

/--
Increase the value at root of the tree by `k`.

NOTE: this corresponds to increasing the entire represented function by `k`.
-/
def lift (k : Nat) : EventTree → EventTree
  | leaf n => leaf (n + k)
  | node n l r => node (n + k) l r

/--
Decrease the value of the represented function by `k`.

This will try to decrease just the value at the root of the tree, but if this
value is smaller than `k`, we will have to recurse.
-/
def sink (k : Nat) : EventTree → EventTree
  | leaf n => leaf (n - k)
  | node n l r =>
    node (n - k) (l.sink (k - n)) (r.sink (k - n))

/-- Return the minimal value of the function represented by an EventTree. -/
def minValue : EventTree → Nat
  | leaf n => n
  | node m l r => m + (min l.minValue r.minValue)

/-- Return the maximal value of the function represented by an EventTree. -/
def maxValue : EventTree → Nat
  | leaf n => n
  | node m l r => m + (max l.maxValue r.maxValue)

/-- The depth of the tree; primarily used a termination measure. -/
def depth : EventTree → Nat
  | leaf _ => 1
  | node _ l r => 1 + max l.depth r.depth

section BasicLemmas
variable {e : EventTree} {l r : EventTree} {n m k : Nat}

attribute [local grind] lift sink

@[simp, grind =] theorem rootValue_leaf : (leaf n).rootValue = n := rfl
@[simp, grind =] theorem rootValue_node : (node n l r).rootValue = n := rfl

@[simp, grind =] theorem minValue_leaf : (leaf n).minValue = n := rfl
@[simp, grind =] theorem minValue_node : (node n l r).minValue = n + min l.minValue r.minValue := rfl

@[simp, grind =] theorem maxValue_leaf : (leaf n).maxValue = n := rfl
@[simp, grind =] theorem maxValue_node : (node n l r).maxValue = n + max l.maxValue r.maxValue := rfl

@[simp, grind =] theorem lift_zero : e.lift 0 = e := by cases e <;> rfl
@[simp, grind =] theorem sink_zero : e.sink 0 = e := by
  induction e <;> grind

@[simp, grind =] theorem lift_leaf : (leaf n).lift k = leaf (n + k) := rfl
@[simp, grind =] theorem lift_node : (node n l r).lift k = node (n + k) l r := rfl

@[simp, grind =] theorem sink_leaf : (leaf n).sink k = leaf (n - k) := rfl
@[simp, grind =] theorem sink_node : (node n l r).sink k = node (n - k) (l.sink (k - n)) (r.sink (k - n)) := by grind

@[simp, grind =] theorem rootValue_lift : (e.lift k).rootValue = e.rootValue + k := by cases e <;> rfl
@[simp, grind =] theorem rootValue_sink : (e.sink k).rootValue = e.rootValue - k := by cases e <;> rfl

@[simp, grind =] theorem minValue_lift : (e.lift k).minValue = e.minValue + k := by cases e <;> grind
@[simp, grind =] theorem maxValue_lift : (e.lift k).maxValue = e.maxValue + k := by cases e <;> grind

@[simp, grind =] theorem minValue_sink : (e.sink k).minValue = e.minValue - k := by
  induction e generalizing k <;> grind
@[simp, grind =] theorem maxValue_sink : (e.sink k).maxValue = e.maxValue - k := by
  induction e generalizing k <;> grind

@[simp, grind =] theorem lift_lift : (e.lift k).lift m = e.lift (k + m) := by cases e <;> grind
@[simp, grind =] theorem sink_sink : (e.sink k).sink m = e.sink (k + m) := by
  induction e generalizing k m <;> grind

@[simp] theorem rootValue_le_maxValue : e.rootValue ≤ e.maxValue := by cases e <;> grind
grind_pattern rootValue_le_maxValue => e.rootValue, e.maxValue

@[simp] theorem minValue_le_maxValue : e.minValue ≤ e.maxValue := by induction e <;> grind
grind_pattern minValue_le_maxValue => e.minValue, e.maxValue

@[simp, grind =] theorem depth_leaf : (leaf n).depth = 1 := rfl
@[simp, grind =] theorem depth_node : (node n l r).depth = 1 + max l.depth r.depth := rfl
@[simp, grind =] theorem depth_lift : depth (e.lift k) = depth e := by
  cases e <;> rfl

end BasicLemmas
end Defs

/-!
## Normal Forms
Section 5.2 of [1]
-/

/--
Normalize an event tree to its canonical form.

In a normalized `node n l r`, either `l.minValue` or `r.minValue` should be zero.
This also imples that for a normalized EventTree `e`, we have that the minimal
value coincides with the root value (`e.minValue = e.rootValue`).
-/
def normalize : EventTree → EventTree
  | leaf n => leaf n
  | node n l r =>
    let l' := l.normalize
    let r' := r.normalize
    let minVal := min l'.rootValue r'.rootValue
    node (n + minVal) (l'.sink minVal) (r'.sink minVal)

/-!
## Lemmas
-/
section Lemmas
variable {e : EventTree} {l r : EventTree} {n m k : Nat}

attribute [local grind] normalize

@[simp, grind =] theorem normalize_leaf : (leaf n).normalize = leaf n := rfl
@[grind =] theorem normalize_node :
    (node n l r).normalize
    = let l' := l.normalize
      let r' := r.normalize
      let minVal := min l'.rootValue r'.rootValue
      node (n + minVal) (l'.sink minVal) (r'.sink minVal) :=
  rfl

@[simp, grind =] theorem normalize_rootValue : e.normalize.rootValue = e.minValue := by
  induction e <;> grind

@[simp, grind =] theorem normalize_maxValue : e.normalize.maxValue = e.maxValue := by
  induction e <;> grind

@[simp, grind =] theorem normalize_minValue : e.normalize.minValue = e.minValue := by
  induction e <;> grind

@[simp, grind =] theorem normalize_sink : (e.sink k).normalize = (e.normalize).sink k := by
  induction e generalizing k <;> grind

@[simp, grind =] theorem normalize_lift : (e.lift k).normalize = (e.normalize).lift k := by
  cases e <;> grind

@[simp] theorem normalize_normalize : (e.normalize).normalize = e.normalize := by
  stop
  induction e with
  | leaf n => rfl
  | node n l r ihl ihr =>
    simp [normalize]
    grind

end Lemmas

/-!
## Denotation
-/
section Denote

def denote : EventTree → Rat → Nat
  | .leaf n, x => if 0 ≤ x ∧ x < 1 then n else 0
  | .node n l r, x =>
    if 0 ≤ x ∧ x < 1 then
      n + l.denote (2 * x) + r.denote (2 * x - 1)
    else
      0

section DenoteLemmas
variable {e : EventTree} {l r : EventTree} {n : Nat} {x : Rat}

attribute [local grind] denote

@[simp, grind =] theorem denote_leaf_of (hx : 0 ≤ x ∧ x < 1) : (leaf n).denote x = n := by grind
@[simp, grind =] theorem denote_node_of (hx : 0 ≤ x ∧ x < 1) :
    (node n l r).denote x = n + l.denote (2 * x) + r.denote (2 * x - 1) := by
  grind

end DenoteLemmas
end Denote

/-
TODO: the comparison and join sections should be moved to the Clock.lean file
This file is just for the basic setup
-/

/-!
## Comparison (≤)
-/
section Comparison

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


end EventTree
end EffectSSA.ITC
