import EffectSSA.ITC.CanonicalIdTree
import EffectSSA.ITC.CanonicalEventTree
import EffectSSA.ITC.Denote

import Batteries.Util.ProofWanted

/-!
# Simplified Interval Tree Clock

We combine a (canonical) id tree with an event counter to obtain our simplification
of the interval tree clock. [1]

Referenes:
[1]: Almeida et al. "Interval Tree Clocks: A Logical Clock for Dynamic Systems"
-/
namespace EffectSSA.ITC

/--
A clock combines a (canonical) id tree with an event counter.
-/
structure Clock where
  /--
  `i` is the id component.

  The id determines whether two threads are concurrent.
  -/
  i : CanonicalIdTree
  /--
  `e` tracks the maximal number of splits (or merges, TBD) which have occured
  in any one path in the history of the current thread.

  This is used to disambiguate between two non-concurrent threads,
  which thread precedes the other.
  -/
  e : CanonicalEventTree
  deriving DecidableEq


/-!
## Comparison
Section 5.3.1 in [1]
-/
section Compare

namespace CanonicalEventTree
/--
We say that `e₁ ≤ e₂` for two (canonical) event trees `e₁` and `e₂`, when
  `⟦e₁⟧(x) ≤ ⟦e₂⟧(x)` for every `x ∈ [0, 1)`
-/
def le (e₁ : CanonicalEventTree) (e₂ : CanonicalEventTree) : Bool :=
  go e₁.raw e₂.raw
  where
    go : EventTree → EventTree → Bool
    | .leaf n₁, e₂    => n₁ ≤ e₂.rootValue
    -- At this point, we deviate from the paper by decrementing the rhs, rather than lifting
    -- the lhs; this is logically equivalent, but our version is structurally recursive in the
    -- first argument, and thus nicer for the termination checker
    | .node n₁ l₁ r₁, .leaf n₂       => n₁ ≤ n₂ && go l₁ (.leaf (n₂ - n₁))   && go r₁ (.leaf (n₂ - n₁))
    | .node n₁ l₁ r₁, .node n₂ l₂ r₂ => n₁ ≤ n₂ && go l₁ (l₂.lift (n₂ - n₁)) && go r₁ (r₂.lift (n₂ - n₁))
instance : LE CanonicalEventTree where le e₁ e₂ := e₁.le e₂

section LELemmas
variable {e e₁ e₂ : CanonicalEventTree} {l₁ r₁ l₂ r₂ : CanonicalEventTree} {n₁ n₂ : Nat}

attribute [local grind, local simp] le le.go
theorem le_iff' : (e₁ ≤ e₂) ↔ e₁.le e₂ = true := by
  simp [LE.le]

instance : DecidableLE CanonicalEventTree := by
  intro e₁ e₂
  apply decidable_of_bool (e₁.le e₂)
  rfl

/-! #### Basic LE lemmas -/
section Basic

@[simp, grind =] theorem leaf_le : leaf n₁ ≤ e₂ ↔ n₁ ≤ e₂.rootValue := by grind [le_iff']
@[simp, grind =] theorem le_leaf : e₁ ≤ leaf n₂ ↔ e₁.maxValue ≤ n₂ := by
  induction e₁ generalizing n₂ <;> simp_all [le_iff']; grind

@[simp, grind .] theorem zero_le : zero ≤ e₂ := by cases e₂ <;> grind

@[simp, grind =] theorem node_le_node {hmin₁ hmin₂} :
    (node n₁ l₁ r₁ hmin₁ ≤ node n₂ l₂ r₂ hmin₂)
    ↔ n₁ ≤ n₂ ∧ l₁ ≤ (l₂.lift (n₂ - n₁)) ∧ r₁ ≤ (r₂.lift (n₂ - n₁)) := by
  grind [le_iff']

-- @[simp, grind =] theorem node'_le_node {hmin₂} :
--     (node' n₁ l₁ r₁ ≤ node n₂ l₂ r₂ hmin₂)
--     ↔ n₁ ≤ n₂ ∧ l₁ ≤ (l₂.lift (n₂ - n₁)) ∧ r₁ ≤ (r₂.lift (n₂ - n₁)) := by
--   grind [le_iff']

@[grind →] theorem rootValue_le_of_le (h : e₁ ≤ e₂) : e₁.rootValue ≤ e₂.rootValue := by
  cases e₁ <;> cases e₂ <;> grind

@[grind! .]
theorem le_lift (e : CanonicalEventTree) (k) : e ≤ e.lift k := by
  induction e generalizing k <;> grind

theorem le_of_maxValue_le_rootValue (h : e₁.maxValue ≤ e₂.rootValue) : e₁ ≤ e₂ := by
  induction e₁ generalizing e₂ <;> cases e₂ <;> simp_all <;> grind

@[grind →]
theorem maxValue_le_maxValue_of_le (h : e₁ ≤ e₂) : e₁.maxValue ≤ e₂.maxValue := by
  induction e₁ generalizing e₂ <;> cases e₂ <;> simp_all <;> grind

/--
The characteristic equation of `≤` on event trees
-/
theorem le_iff_denote_le : e₁ ≤ e₂ ↔ ∀ x, e₁.denote x ≤ e₂.denote x := by
  sorry

end Basic

/-! #### Reflexivity and Transitivity -/

@[simp, grind .] theorem le_refl : e ≤ e := by induction e <;> grind
theorem le_trans : e₁ ≤ e₂ → e₂ ≤ e₃ → e₁ ≤ e₃ := by grind [le_iff_denote_le]

instance : Std.IsPreorder CanonicalEventTree where
  le_refl _ := le_refl
  le_trans _ _ _ := le_trans

-- NOTE: we deliberately put `le_iff` just before closing the namespace, as it
--       would otherwise cause divergence with the local `le_iff'` simp-lemma.
@[simp, grind =] theorem le_iff : (e₁.le e₂ = true) ↔ (e₁ ≤ e₂) := by
  simp [LE.le]

end LELemmas
end CanonicalEventTree

/--
We say that `i ≤ j`, for two (canonical) id trees `i` and `j`, when the set
represented by `i` is a *subset* of the set represented by `j`.

NOTE: this is unused, since we've introduced the full event tree
-/
def CanonicalIdTree.le (i : CanonicalIdTree) (j : CanonicalIdTree) : Bool :=
  go i.raw j.raw
  where
    go : IdTree → IdTree → Bool
    | .zero, _ => true
    | _, .one  => true
    | .node l₁ r₁, .node l₂ r₂ => go l₁ l₂ ∧ go r₁ r₂
    | _, _ => false
instance : LE CanonicalIdTree where le i j := i.le j

instance : LE Clock where le c₁ c₂ := c₁.e ≤ c₂.e

section CompareLemmas
variable {i j : CanonicalIdTree} {c₁ c₂ : Clock}

/-! ### CanonicalIdTree LE lemmas -/
namespace CanonicalIdTree

attribute [local grind] le le.go
@[local simp, local grind =] theorem le_iff' : (i ≤ j) ↔ i.le j = true := by
  simp [LE.le]

instance : DecidableLE CanonicalIdTree := by
  intro i j
  apply decidable_of_bool (i.le j)
  rfl

@[simp, grind .] theorem zero_le : zero ≤ i := by rfl
@[simp, grind .] theorem le_one : i ≤ one := by cases i <;> rfl


@[simp, grind .] theorem one_le_iff : one ≤ i ↔ i = one := by grind
@[simp, grind .] theorem le_zero_iff : i ≤ zero ↔ i = zero := by grind

@[simp, grind .] theorem node_le_node_iff {l₁ r₁ l₂ r₂ : CanonicalIdTree} {hz₁ ho₁ hz₂ ho₂} :
    (node l₁ r₁ hz₁ ho₁) ≤ (node l₂ r₂ hz₂ ho₂) ↔ l₁ ≤ l₂ ∧ r₁ ≤ r₂ := by
  grind

@[simp, grind .] theorem node_le_node'_iff {l₁ r₁ l₂ r₂ : CanonicalIdTree} {hz ho} :
    node l₁ r₁ hz ho ≤ node' l₂ r₂ ↔ l₁ ≤ l₂ ∧ r₁ ≤ r₂ := by
  by_cases ho : l₂ = zero ∧ r₂ = zero
  · grind
  by_cases hz : l₂ = one ∧ r₂ = one
  <;> grind

@[simp, grind .] theorem le_refl : i ≤ i := by induction i <;> grind
@[simp, grind .] theorem le_trans {i₁ i₂ i₃ : CanonicalIdTree} : i₁ ≤ i₂ → i₂ ≤ i₃ → i₁ ≤ i₃ := by
  induction i₁ generalizing i₂ i₃ <;> try grind
  cases i₂ <;> try grind
  cases i₃ <;> grind

instance : Std.IsPreorder CanonicalIdTree where
  le_refl _ := le_refl
  le_trans _ _ _ := le_trans

-- NOTE: we deliberatelyy put `le_iff` just before closing the namespace, as it
--       would otherwise cause divergence with the local `le_iff'` simp-lemma.
@[simp, grind =] theorem le_iff : (i.le j = true) ↔ (i ≤ j) := by
  simp [LE.le]

end CanonicalIdTree

/-! ### Clock LE lemmas -/
namespace Clock
variable {e : Nat}

@[simp, grind =] theorem le_iff : c₁ ≤ c₂ ↔ c₁.e ≤ c₂.e := by rfl

instance : DecidableLE Clock := fun _ _ => decidable_of_iff' _ le_iff

@[simp, grind .] theorem le_refl : c₁ ≤ c₁ := by grind

-- TODO: reinstate the below lemmas, if needed?
-- @[simp, grind .] theorem zero_le_iff : ⟨.zero, e⟩ ≤ c₁ ↔ c₁.e < e := by grind
-- @[simp, grind .] theorem le_one_iff : c₁ ≤ ⟨.one, e⟩ ↔ c₁.e ≤ e := by grind

end Clock
end CompareLemmas
end Compare

/-!
## Unrelated
We're especially interested in whether two clocks are unrelated (in either
direction), for which we introduce a short-hand `x # y` (not present in [1]).
-/
section Unrel

/--
`x # y` is short for `¬(x ≤ y) ∧ ¬(y ≤ x)`

The preferred spelling in theorems is `unrel`
-/
def Unrelated {α} [LE α] (x y : α) : Prop := ¬(x ≤ y) ∧ ¬(y ≤ x)
@[inherit_doc] infix:67 " # " => Unrelated

section UnrelLemmas

/-! ### Generic Unrelated lemmas -/
section GenericUnrelLemmas
variable {α : Type _} [LE α] {x y : α}

@[grind =] theorem unrel_iff : x # y ↔ ¬(x ≤ y) ∧ ¬(y ≤ x) := by rfl
@[grind =] theorem not_unrel_iff : ¬(x # y) ↔ x ≤ y ∨ y ≤ x := by grind

instance [DecidableLE α] : Decidable (x # y) := by unfold Unrelated; infer_instance

/-- `#` is symmetric -/
theorem unrel_symm : x # y ↔ y # x := by grind
instance : Std.Symm (@Unrelated α _) where
  symm _ _ := @unrel_symm.mp

/-!
`#` is irreflexive (when `≤` is reflexive)
-/

theorem unrel_refl_iff : x # x ↔ ¬(x ≤ x) := by grind

@[simp, grind .] theorem unrel_irrefl [Std.Refl (@LE.le α _)] (x : α) : ¬(x # x) := by
  simp [unrel_refl_iff, Std.Refl.refl]
instance [Std.Refl (@LE.le α _)] : Std.Irrefl (@Unrelated α _) where irrefl := unrel_irrefl

end GenericUnrelLemmas

variable {i j : CanonicalIdTree} {c₁ c₂ : Clock}

/-! ### CanonicalIdTree Unrelated lemmas -/
namespace CanonicalIdTree

@[simp, grind .] theorem unrel_irrefl : ¬(i # i) := by grind

@[simp, grind .] theorem not_unrel_zero : ¬(i # zero) := by grind
@[simp, grind .] theorem not_zero_unrel : ¬(zero # j) := by grind

@[simp, grind .] theorem not_unrel_one : ¬(i # one) := by grind
@[simp, grind .] theorem not_one_unrel : ¬(one # j) := by grind

@[simp, grind .] theorem node_unrel_node_iff {l₁ r₁ l₂ r₂ : CanonicalIdTree} {hz₁ ho₁ hz₂ ho₂} :
    (node l₁ r₁ hz₁ ho₁) # (node l₂ r₂ hz₂ ho₂) ↔
      l₁ # l₂ ∨ r₁ # r₂ ∨ (¬l₁ ≤ l₂ ∧ ¬r₂ ≤ r₁) ∨ (¬r₁ ≤ r₂ ∧ ¬l₂ ≤ l₁) := by grind

end CanonicalIdTree

/-! ### Clock Unrelated lemmas -/
namespace Clock

/-- Two clocks are unrelated iff their event components are unrelated -/
@[simp, grind =] theorem unrel_iff_unrel : c₁ # c₂ ↔ c₁.e # c₂.e := by grind

end Clock
end UnrelLemmas
end Unrel

/-!
## Fork
Section 5.3.2 of [1]
-/
section Fork

namespace IdTree
def split : IdTree → IdTree × IdTree
  | zero => (zero, zero)
  | one => (.node one zero, .node zero one)
  | node zero i =>
      let i := split i
      (node zero i.1, node zero i.2)
  | node i zero =>
      let i := split i
      (node i.1 zero, node i.2 zero)
  | node i₁ i₂ => (node i₁ zero, node zero i₂)

section SplitLemmas
variable {i : IdTree}

@[simp, grind =] theorem split_zero : split zero = (zero, zero) := rfl
@[simp, grind =] theorem split_one : split one = (.node one zero, .node zero one) := rfl
@[simp, grind =] theorem split_node_zero  : split (node zero i) = (node zero (split i).1, node zero (split i).2) := rfl
@[simp, grind =] theorem split_zero_node : split (node i zero) = (node (split i).1 zero, node (split i).2 zero) := by
  cases i <;> rfl

@[simp, grind =] theorem split_node_node {i₁ i₂ : IdTree} (h₁ : i₁ ≠ zero) (h₂ : i₂ ≠ zero) :
    split (node i₁ i₂) = (node i₁ zero, node zero i₂) := by
  simp only [split]

@[simp, grind =] theorem split_fst_eq_zero_iff : (split i).1 = zero ↔ i = zero := by
  cases i with
  | node l r => cases l <;> cases r <;> grind
  | _ => simp
@[simp, grind =] theorem split_snd_eq_zero_iff : (split i).2 = zero ↔ i = zero := by
  cases i with
  | node l r => cases l <;> cases r <;> grind
  | _ => simp

@[simp, grind =] theorem normalize_split_fst (hi : i.normalize = i) :
    (split i).1.normalize = (split i).1 := by
  fun_induction IdTree.split i <;> grind

@[simp, grind =] theorem normalize_split_snd (hi : i.normalize = i) :
    (split i).2.normalize = (split i).2 := by
  fun_induction IdTree.split i <;> grind

end SplitLemmas
end IdTree

namespace CanonicalIdTree
def split (i : CanonicalIdTree) : CanonicalIdTree × CanonicalIdTree :=
  let is := i.raw.split
  (⟨is.1, by grind⟩, ⟨is.2, by grind⟩)

section SplitLemmas
variable {i : CanonicalIdTree}

@[simp] theorem split_mk {t : IdTree} {h : t.normalize = t} :
    split ⟨t, h⟩ = (⟨t.split.1, by grind⟩, ⟨t.split.2, by grind⟩) := by
  grind [split]

@[simp, grind =] theorem raw_split_fst : (split i).1.raw = i.raw.split.1 := by simp [split]
@[simp, grind =] theorem raw_split_snd : (split i).2.raw = i.raw.split.2 := by simp [split]

/-- Custom functional induction principle for `CanonicalIdTree.split`. -/
theorem split.induct_unfolding (motive : CanonicalIdTree → CanonicalIdTree × CanonicalIdTree → Prop)
    (case1 : motive zero (zero, zero))
    (case2 : ∀ ho hz, motive one (node one zero hz ho, node zero one (by simp) (by simp)))
    (case3 : ∀ (i : CanonicalIdTree) (hi : i ≠ .zero),
      motive i (split i) → ∀ hz ho, motive (node zero i hz ho)
        (node zero (split i).1, node zero (split i).2))
    (case4 : ∀ (i : CanonicalIdTree) (hi : i.raw ≠ .zero),
      motive i (split i) →
      ∀ hz ho, motive (node i zero hz ho)
        (node (split i).1 zero, node (split i).2 zero))
    (case5 : ∀ (i₁ i₂ : CanonicalIdTree) (h₁ : i₁ ≠ .zero) (h₂ : i₂ ≠ .zero),
      ∀ hz ho, motive (node i₁ i₂ hz ho)
        (node i₁ zero, node zero i₂))
    (i : CanonicalIdTree) : motive i (split i) := by
  rcases i with ⟨i, hi⟩
  simp only [split_mk]
  fun_induction IdTree.split i <;> grind

@[simp, grind =] theorem split_fst_eq_zero_iff : i.split.fst = .zero ↔ i = .zero := by grind
@[simp, grind =] theorem split_snd_eq_zero_iff : i.split.snd = .zero ↔ i = .zero := by grind

theorem split_le : (split i).1 ≤ i ∧ (split i).2 ≤ i := by
  induction i using split.induct_unfolding <;> grind

@[simp, grind .] theorem split_fst_le : (split i).1 ≤ i := split_le.1
@[simp, grind .] theorem split_snd_le : (split i).2 ≤ i := split_le.2

theorem not_le_split (h : i ≠ zero) : ¬(i ≤ i.split.1) ∧ ¬(i ≤ i.split.2) := by
  induction i using split.induct_unfolding <;> grind

@[simp, grind .] theorem not_le_split_fst (h : i ≠ zero) : ¬(i ≤ i.split.1) := (not_le_split h).1
@[simp, grind .] theorem not_le_split_snd (h : i ≠ zero) : ¬(i ≤ i.split.2) := (not_le_split h).2

@[simp, grind .] theorem indep_split (h : i ≠ zero) : i.split.fst # i.split.snd := by
  induction i using split.induct_unfolding <;> grind

@[grind →]
theorem denote_split_fst_of_snd : i.split.snd.denote x = true → i.split.fst.denote x = false := by
  sorry

@[grind →]
theorem denote_split_snd_of_fst : i.split.fst.denote x = true → i.split.snd.denote x = false := by
  sorry

end SplitLemmas
end CanonicalIdTree

namespace CanonicalEventTree
attribute [scoped grind =] Nat.min_eq_left Nat.min_eq_right

/--
Expand a leaf into an equivalent (non-canonical) node, or return an existing
node as-is
-/
def intoNode (e : CanonicalEventTree) : Nat × CanonicalEventTree × CanonicalEventTree :=
  match he : e.raw with
  | .leaf n => (n, .leaf 0, .leaf 0)
  | .node n l r => (n, ⟨l, by grind [eq_normalize]⟩, ⟨r, by grind [eq_normalize]⟩)

/--
Increment the left-most branch of the event-tree that is within the domain
allowed to be incremented by the given id-tree.

Returns the event-tree unchanged if `id` represents the empty domain.
-/
def increment (id : CanonicalIdTree) : CanonicalEventTree → CanonicalEventTree :=
  go id.raw
  where go : IdTree → CanonicalEventTree → CanonicalEventTree
  | .zero, e          => e
  | .one, e           => e.lift 1
  | .node i₁ i₂, e  =>
      let (n, l, r) := e.intoNode
      if i₁ = .zero then
        node' n l (go i₂ r)
      else
        node' n (go i₁ l) r

section IncrLemmas
variable {id : CanonicalIdTree} {e l r: CanonicalEventTree} {n : Nat}

@[simp, grind =] theorem intoNode_leaf : intoNode (leaf n) = (n, leaf 0, leaf 0) := rfl
@[simp, grind =] theorem intoNode_node {hmin} : intoNode (node n l r hmin) = (n, l, r) := rfl

@[simp, grind =] theorem increment_zero : increment .zero e = e := rfl
@[simp, grind =] theorem increment_one : increment .one e = e.lift 1 := rfl

@[grind =] theorem increment_node {l r : CanonicalIdTree} {hz ho} :
  increment (.node l r hz ho) e
  = let (n, le, re) := e.intoNode
    if l = .zero then
      .node' n le (increment r re)
    else
      .node' n (increment l le) re := by simp; rfl

@[simp, grind =] theorem increment_node_zero {i : CanonicalIdTree} {hz ho} :
    increment (.node .zero i hz ho) e
    = let (n, l, r) := e.intoNode
      node' n l (increment i r) := rfl

/--
`increment` either increases the value at point `x`, or leaves it as-is.
Thus, at every point, the original value is less than or equal to the new value.
-/
@[simp] theorem denote_le_denote_increment :
    e.denote x ≤ (e.increment id).denote x := by
  sorry
grind_pattern denote_le_denote_increment => e.denote x, (e.increment id).denote x

/--
If the `id` is non-zero, then `increment` increased the value at atleast one
point, thus there exists some point `x` in the domain represented by `id`, at
which the new value is strictly larger.
-/
@[simp] theorem exists_denote_lt_denote_increment (h : id ≠ .zero) :
    ∃ x, id.denote x.val ∧ e.denote x < (e.increment id).denote x := by
  sorry
grind_pattern exists_denote_lt_denote_increment => e.denote, (e.increment id).denote

/--
`increment` does not change any value that is outside of the domain allowed by
the given `id`.
-/
@[simp, grind =] theorem denote_increment_eq_of (h : id.denote x.val = false) :
    (e.increment id).denote x = e.denote x := by
  sorry

@[grind .] theorem le_increment (e : CanonicalEventTree) :
    e ≤ e.increment id := by
  grind [le_iff_denote_le]

end IncrLemmas
end CanonicalEventTree

namespace Clock
def fork (c : Clock) : Clock × Clock :=
  let (i₁, i₂) := c.i.split
  let e₁ := c.e.increment i₁
  let e₂ := c.e.increment i₂
  (⟨i₁, e₁⟩, ⟨i₂, e₂⟩)

section ForkLemmas
open CanonicalEventTree
variable (c c' : Clock)

@[simp, grind =] theorem i_fork_fst : c.fork.1.i = (c.i.split).1 := by rfl
@[simp, grind =] theorem i_fork_snd : c.fork.2.i = (c.i.split).2 := by rfl
@[simp, grind =] theorem e_fork_fst : c.fork.1.e = c.e.increment (c.i.split).1 := by rfl
@[simp, grind =] theorem e_fork_snd : c.fork.2.e = c.e.increment (c.i.split).2 := by rfl

/-!
`c` (strictly) happens-before both results of `c.fork`
-/
@[simp, grind .] theorem le_fork_snd : c ≤ c.fork.snd := by grind
@[simp, grind .] theorem le_fork_fst : c ≤ c.fork.fst := by grind

@[simp, grind .] theorem not_fork_fst_le (h : c.i ≠ .zero) : ¬(c.fork.fst ≤ c) := by
  have := c.e.exists_denote_lt_denote_increment h
  grind [le_iff_denote_le]

@[simp, grind .] theorem not_fork_snd_le (h : c.i ≠ .zero) : ¬(c.fork.snd ≤ c) := by
  have := c.e.exists_denote_lt_denote_increment h
  grind [le_iff_denote_le]

/--
The results of a `fork` are independent.
-/
theorem indep_fork (h : c.i ≠ .zero) : c.fork.fst # c.fork.snd := by
  have ⟨x₁, hx₁⟩ := c.e.exists_denote_lt_denote_increment (id := c.i.split.fst) <| by grind
  have ⟨x₂, hx₂⟩ := c.e.exists_denote_lt_denote_increment (id := c.i.split.snd) <| by grind
  grind [le_iff_denote_le]

variable {c c'} in
/--
If `c` is independent from `c'`, then the same holds for either result of `c.fork`.
-/
proof_wanted indep_fork_congr (h : c # c') : c.fork.fst # c' ∧ c.fork.snd # c'

end ForkLemmas
end Clock
end Fork
/-!
## Join
Section 5.3.3 of [1]
-/
section Join

namespace IdTree
def sum : IdTree → IdTree → IdTree
  | zero, i | i, zero => i
  | one, _i | _i, one => one
  | node l₁ r₁, node l₂ r₂ =>
    let l := sum l₁ l₂
    let r := sum r₁ r₂
    normalize (node l r)

section SumLemmas
variable {i₁ i₂ : IdTree}

@[simp, grind =] theorem zero_sum : sum zero i₂ = i₂ := by rfl
@[simp, grind =] theorem sum_zero : sum i₁ zero = i₁ := by cases i₁ <;> rfl
@[simp, grind =] theorem one_sum : sum one i₂ = one := by cases i₂ <;> rfl
@[simp, grind =] theorem sum_one : sum i₁ one = one := by cases i₁ <;> rfl

@[simp, grind =] theorem node_sum_node {l₁ r₁ l₂ r₂ : IdTree} :
    sum (node l₁ r₁) (node l₂ r₂) = normalize (node (sum l₁ l₂) (sum r₁ r₂)) := by rfl

@[simp, grind =] theorem normalize_sum (h₁ : i₁.normalize = i₁) (h₂ : i₂.normalize = i₂) :
    (sum i₁ i₂).normalize = sum i₁ i₂ := by
  fun_induction sum i₁ i₂ <;> grind

end SumLemmas
end IdTree

namespace CanonicalIdTree
def sum (i₁ : CanonicalIdTree) (i₂ : CanonicalIdTree) : CanonicalIdTree :=
  ⟨.sum i₁.raw i₂.raw, by grind⟩

section SumLemmas
variable {i₁ i₂ : CanonicalIdTree}

@[simp] theorem sum_mk {t₁ t₂ : IdTree} {h₁ : t₁.normalize = t₁} {h₂ : t₂.normalize = t₂} :
    sum ⟨t₁, h₁⟩ ⟨t₂, h₂⟩ = ⟨t₁.sum t₂, by grind⟩ := rfl

/-- Custom functional induction principle for `CanonicalIdTree.sum`. -/
theorem sum.induct_unfolding (motive : CanonicalIdTree → CanonicalIdTree → CanonicalIdTree → Prop)
    (case1 : ∀ i, motive zero i i)
    (case2 : ∀ i, motive i zero i)
    (case3 : ∀ i, motive one i one)
    (case4 : ∀ i, motive i one one)
    (case5 : ∀ (l₁ r₁ l₂ r₂ : CanonicalIdTree) hz₁ ho₁ hz₂ ho₂,
      motive l₁ l₂ (sum l₁ l₂) →
      motive r₁ r₂ (sum r₁ r₂) →
      motive (node l₁ r₁ hz₁ ho₁) (node l₂ r₂ hz₂ ho₂)
        (node' (sum l₁ l₂) (sum r₁ r₂)))
    (i₁ i₂ : CanonicalIdTree) : motive i₁ i₂ (sum i₁ i₂) := by
  rcases i₁ with ⟨i₁, h₁⟩
  rcases i₂ with ⟨i₂, h₂⟩
  simp only [sum_mk]
  fun_induction IdTree.sum i₁ i₂ with
  | case5 l₁ r₁ l₂ r₂ l r ihl ihr =>
      -- TODO: the following should be reducable to just `grind`, with appropriate grind-lemmas
      have : l₁.normalize = l₁ := by grind
      have : l₂.normalize = l₂ := by grind
      have : r₁.normalize = r₁ := by grind
      have : r₂.normalize = r₂ := by grind
      simp [*]
      apply case5 <;> (simp; grind)
  | _ => grind

theorem sum_le : i₁ ≤ sum i₁ i₂ ∧ i₂ ≤ sum i₁ i₂ := by
  induction i₁, i₂ using sum.induct_unfolding <;> grind

@[simp, grind .] theorem le_sum_left : i₁ ≤ sum i₁ i₂ := sum_le.1
@[simp, grind .] theorem le_sum_right : i₂ ≤ sum i₁ i₂ := sum_le.2

@[simp, grind =] theorem sum_eq_zero_iff : sum i₁ i₂ = zero ↔ i₁ = zero ∧ i₂ = zero := by
  induction i₁, i₂ using sum.induct_unfolding <;> simp; grind


/-
TODO: Check if not_sum_lt actually holds, and finish proof
-/
theorem not_sum_lt (h : i₁ # i₂) : ¬(sum i₁ i₂ ≤ i₁) ∧ ¬(sum i₁ i₂ ≤ i₂) := by
  have : i₁ ≠ zero := by grind
  have : i₂ ≠ zero := by grind
  induction i₁, i₂ using sum.induct_unfolding with
  | case5 l₁ r₁ l₂ r₂ hz₁ ho₁ hz₂ ho₂ ihl ihr =>
    sorry
  | _ => grind

-- @[simp, grind .] theorem not_sum_le_left (h₁ : i₁ ≠ zero) (h₂ : i₂ ≠ zero) : ¬(sum i₁ i₂ ≤ i₁) :=
--   (not_sum_le h₁ h₂).1
-- @[simp, grind .] theorem not_sum_le_right (h₁ : i₁ ≠ zero) (h₂ : i₂ ≠ zero) : ¬(sum i₁ i₂ ≤ i₂) :=
--   (not_sum_le h₁ h₂).2

end SumLemmas
end CanonicalIdTree

/--
`e.liftTo k` returns an event tree where each value will be assigned to the
maximum of the current value and `k`.

This is analogous to `e.join (leaf k)`; we define this as a standalone operation
to avoid the non-structural recursion in the paper definition of join. [1]
-/
def CanonicalEventTree.liftTo (k : Nat) : CanonicalEventTree → CanonicalEventTree
  | leaf n     => .leaf (max n k)
  | e@⟨.node n l r, _⟩ =>
    if n ≤ k then
      node' n (liftTo (k - n) ⟨l, by grind⟩) (liftTo (k - n) ⟨r, by grind⟩)
    else
      e
  termination_by e => e.raw.depth

/--
Join two event trees by assiging each point to the pointwise maximum.

The definition of join in [5] as written doesn't have a clear termination
measure, so we adapt it. In particular, we've introduced `liftTo` for the
action of joining a tree with a leaf (on either side; join is symmetric).
-/
def CanonicalEventTree.join : CanonicalEventTree → CanonicalEventTree → CanonicalEventTree
  | leaf n₁, e₂ => e₂.liftTo n₁
  | e₁, leaf n₂ => e₁.liftTo n₂
  | ⟨.node n₁ l₁ r₁, h₁⟩, ⟨.node n₂ l₂ r₂, h₂⟩ =>
      let l₁ := mk l₁
      let r₁ := mk r₁
      let l₂ := mk l₂
      let r₂ := mk r₂
      if n₁ ≤ n₂ then
        .node' n₁ (join l₁ (l₂.lift (n₂ - n₁))) (join r₁ (r₂.lift (n₂ - n₁)))
      else
        .node' n₂ (join l₂ (l₁.lift (n₂ - n₁))) (join r₂ (r₁.lift (n₂ - n₁)))
  termination_by e₁ e₂ => max e₁.raw.depth e₂.raw.depth


namespace CanonicalEventTree

section JoinLemmas
variable {e₁ e₂ l r : CanonicalEventTree} {x : FRat}

/-! ### liftTo -/

@[simp, grind =] theorem liftTo_leaf : (leaf n).liftTo k = leaf (max n k) := by
  unfold liftTo; rfl
@[simp, grind =] theorem liftTo_node :
    (node n l r h).liftTo k
    = if n ≤ k then
        node' n (liftTo (k - n) l) (liftTo (k - n) r)
      else
        node n l r h := by
  conv => lhs; unfold liftTo
  rfl

/-! ### join -/

@[simp, grind =] theorem leaf_join : (leaf n).join e₂ = e₂.liftTo n := by
  unfold join; rfl
@[simp, grind =] theorem join_leaf : e₁.join (leaf m) = e₁.liftTo m := by
  unfold join; cases e₁ <;> grind [node]

@[simp, grind =] theorem leaf_join_leaf : (leaf n).join (leaf m) = leaf (max m n) := by
  grind

/-! ### denotation -/

@[simp, grind =]
theorem denote_liftTo : (e₁.liftTo k).denote x = max (e₁.denote x) k := by
  induction e₁ generalizing x k <;> grind

@[simp, grind =]
theorem denote_join : (e₁.join e₂).denote x = max (e₁.denote x) (e₂.denote x) := by
  fun_induction e₁.join e₂ generalizing x
  · grind
  · grind
  case case3 n₁ l₁ r₁ h₁ n₂ l₂ r₂ h₁ l₁' r₁' l₂' r₂' _ ihl ihr =>
    have hl₁ (h) : ⟨l₁, h⟩ = l₁' := rfl
    have hr₁ (h) : ⟨r₁, h⟩ = r₁' := rfl
    have hl₂ (h) : ⟨l₂, h⟩ = l₂' := rfl
    have hr₂ (h) : ⟨r₂, h⟩ = r₂' := rfl
    simp [*, FRat.splitRec]
    split
    · grind
    · grind
  case case4 n₁ l₁ r₁ h₁ n₂ l₂ r₂ h₁ l₁' r₁' l₂' r₂' _ ihl ihr =>
    have hl₁ (h) : ⟨l₁, h⟩ = l₁' := rfl
    have hr₁ (h) : ⟨r₁, h⟩ = r₁' := rfl
    have hl₂ (h) : ⟨l₂, h⟩ = l₂' := rfl
    have hr₂ (h) : ⟨r₂, h⟩ = r₂' := rfl
    have : n₂ - n₁ = 0 := by grind
    simp only [denote, this, lift_zero] at ihl ihr
    simp [*, FRat.splitRec]
    split
    · grind
    · grind


/--
`e₁` and `e₂` both happen-before `e₁.join e₂`
-/
theorem le_join (e₁ e₂ : CanonicalEventTree) : e₁ ≤ e₁.join e₂ ∧ e₂ ≤ e₁.join e₂ := by
  grind [le_iff_denote_le]

@[simp, grind .] theorem le_join_fst : e₁ ≤ e₁.join e₂ := (le_join e₁ e₂).1
@[simp, grind .] theorem le_join_snd : e₂ ≤ e₁.join e₂ := (le_join e₁ e₂).2

end JoinLemmas
end CanonicalEventTree

namespace Clock
def join (c₁ : Clock) (c₂ : Clock) : Clock where
  i := .sum c₁.i c₂.i
  e := .join c₁.e c₂.e

section JoinLemmas
variable {c₁ c₂ c' : Clock}

@[simp, grind =] theorem i_join : (c₁.join c₂).i = c₁.i.sum c₂.i := by rfl
@[simp, grind =] theorem e_join : (c₁.join c₂).e = c₁.e.join c₂.e := by rfl

/--
`c₁` and `c₂` both happen-before `c₁.join c₂`, assuming that `c₁ # c₂`
-/
@[simp, grind .] theorem le_join_fst : c₁ ≤ c₁.join c₂ := by grind
@[simp, grind .] theorem le_join_snd : c₂ ≤ c₁.join c₂ := by grind

/--
If `c₁` and `c₂` are both independent from `c'`,
then the same holds for `c₁.join c₂`.
-/
proof_wanted indep_join_congr (h₁ : c₁ # c') (h₂ : c₂ # c') : c₁.join c₂ # c'

end JoinLemmas
end Clock
end Join
