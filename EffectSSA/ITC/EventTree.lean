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

/-- Return the minimal value of the function represented by an EventTree. -/
def minValue : EventTree → Nat
  | leaf n => n
  | node m l r => m + (min l.minValue r.minValue)

/-- Return the maximal value of the function represented by an EventTree. -/
def maxValue : EventTree → Nat
  | leaf n => n
  | node m l r => m + (max l.maxValue r.maxValue)

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
def sink (k : Nat) (e : EventTree) (hk : k ≤ e.rootValue := by grind) : EventTree :=
  match e with
  | leaf n => leaf (n - k)
  | node n l r => node (n - k) l r

/-- The depth of the tree; primarily used a termination measure. -/
def depth : EventTree → Nat
  | leaf _ => 0
  | node _ l r => 1 + max l.depth r.depth

section BasicLemmas
variable {e : EventTree} {l r : EventTree} {n m k : Nat}

attribute [local grind] lift sink

/-! ### rootValue, minValue, maxValue -/

@[simp, grind =] theorem rootValue_leaf : (leaf n).rootValue = n := rfl
@[simp, grind =] theorem rootValue_node : (node n l r).rootValue = n := rfl

@[simp, grind =] theorem minValue_leaf : (leaf n).minValue = n := rfl
@[simp, grind =] theorem minValue_node : (node n l r).minValue = n + min l.minValue r.minValue := rfl

@[simp, grind =] theorem maxValue_leaf : (leaf n).maxValue = n := rfl
@[simp, grind =] theorem maxValue_node : (node n l r).maxValue = n + max l.maxValue r.maxValue := rfl

@[simp] theorem rootValue_le_minValue : e.rootValue ≤ e.minValue := by cases e <;> grind
grind_pattern rootValue_le_minValue => e.rootValue, e.minValue

@[simp] theorem minValue_le_maxValue : e.minValue ≤ e.maxValue := by induction e <;> grind
grind_pattern minValue_le_maxValue => e.minValue, e.maxValue

@[simp] theorem rootValue_le_maxValue : e.rootValue ≤ e.maxValue := by cases e <;> grind
grind_pattern rootValue_le_maxValue => e.rootValue, e.maxValue

/-! ### lift, sink -/

@[simp, grind =] theorem lift_zero : e.lift 0 = e := by cases e <;> rfl
@[simp, grind =] theorem sink_zero : e.sink 0 h = e := by
  induction e <;> grind

@[simp, grind =] theorem lift_leaf : (leaf n).lift k = leaf (n + k) := rfl
@[simp, grind =] theorem lift_node : (node n l r).lift k = node (n + k) l r := rfl

@[simp, grind =] theorem sink_leaf : (leaf n).sink k hk = leaf (n - k) := rfl
@[simp, grind =] theorem sink_node : (node n l r).sink k hk = node (n - k) l r := by grind

@[simp, grind =] theorem rootValue_lift : (e.lift k).rootValue = e.rootValue + k := by cases e <;> rfl
@[simp, grind =] theorem rootValue_sink : (e.sink k hk).rootValue = e.rootValue - k := by cases e <;> rfl

@[simp, grind =] theorem minValue_lift : (e.lift k).minValue = e.minValue + k := by cases e <;> grind
@[simp, grind =] theorem maxValue_lift : (e.lift k).maxValue = e.maxValue + k := by cases e <;> grind

@[simp, grind =] theorem minValue_sink : (e.sink k hk).minValue = e.minValue - k := by
  induction e <;> grind
@[simp, grind =] theorem maxValue_sink : (e.sink k hk).maxValue = e.maxValue - k := by
  induction e <;> grind

@[simp] theorem lift_lift : (e.lift k).lift m = e.lift (k + m) := by cases e <;> grind
@[simp] theorem sink_sink : (e.sink k hk).sink m hm = e.sink (k + m) (by grind) := by
  induction e <;> grind
-- ^^ Adding `sink_sink` to the global grind set seems to cause a cycle in grind
--    Thus, we keep it out of the grind-set, and only reintroduce it locally

@[simp] theorem sink_lift : (e.lift k).sink m hk = if k ≤ m then e.sink (m - k) (by grind) else e.lift (k - m) := by
  cases e <;> grind

@[simp] theorem sink_eq_self : e.sink k hk = e ↔ k = 0 := by grind

@[simp] theorem lift_inj : lift k e₁ = lift k e₂ ↔ e₁ = e₂ := by
  cases e₁ <;> cases e₂ <;> simp

@[simp] theorem sink_inj : sink k e₁ hk₁ = sink k e₂ hk₂ ↔ e₁ = e₂ := by
  cases e₁ <;> cases e₂ <;> simp <;> grind

/-! ### depth -/

@[simp, grind =] theorem depth_leaf : (leaf n).depth = 0 := rfl
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

@[simp, grind =] theorem rootValue_normalize : e.normalize.rootValue = e.minValue := by
  induction e <;> grind
@[simp, grind =] theorem maxValue_normalize : e.normalize.maxValue = e.maxValue := by
  induction e <;> grind
@[simp, grind =] theorem minValue_normalize : e.normalize.minValue = e.minValue := by
  induction e <;> grind

@[simp, grind =] theorem normalize_sink : (e.sink k hk).normalize = (e.normalize).sink k (by grind) := by
  induction e generalizing k <;> grind

@[simp, grind =] theorem normalize_lift : (e.lift k).normalize = (e.normalize).lift k := by
  cases e <;> grind

@[simp, grind =] theorem normalize_normalize : (e.normalize).normalize = e.normalize := by
  induction e <;> grind [sink_sink]


end Lemmas

/-!
## Denotation
An EventTree represent a function `Rat → Nat`.
-/
section Denote

/--
`denote` interprets an EventTree as a function `Rat → Nat`, where in particular
any `x : Rat` not in the interval `[0,1)` gets mapped to `0`.
-/
def denote : EventTree → Rat → Nat
  | .leaf n, x => if 0 ≤ x ∧ x < 1 then n else 0
  | .node n l r, x =>
    if 0 ≤ x ∧ x < 0.5 then
      n + l.denote (2 * x)
    else if 0.5 ≤ x ∧ x < 1 then
      n + r.denote (2 * x - 1)
    else
      0

section DenoteLemmas
variable {e : EventTree} {l r : EventTree} {n : Nat} {x : Rat}

attribute [local grind] denote

@[grind =] theorem denote_leaf : (leaf n).denote x = if 0 ≤ x ∧ x < 1 then n else 0 := by rfl
@[grind =] theorem denote_node :
    (node n l r).denote x
    = if 0 ≤ x ∧ x < 0.5 then
        n + l.denote (2 * x)
      else if 0.5 ≤ x ∧ x < 1 then
        n + r.denote (2 * x - 1)
      else
        0 := by rfl

@[simp, grind =] theorem denote_sink : (e.sink k hk).denote x = e.denote x - k := by
  cases e <;> grind

@[simp, grind! .] theorem rootValue_le_denote (hx : 0 ≤ x ∧ x < 1) :
    e.rootValue ≤ e.denote x := by
  cases e <;> grind

@[simp, grind =]
theorem denote_normalize : e.normalize.denote = e.denote := by
  funext x; induction e generalizing x <;> grind

end DenoteLemmas
end Denote

end EventTree
end EffectSSA.ITC
