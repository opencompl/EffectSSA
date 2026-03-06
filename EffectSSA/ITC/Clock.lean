import EffectSSA.ITC.CanonicalIdTree

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
  e : Nat
  deriving DecidableEq


/-!
## Comparison
Section 5.3.1 in [1]
-/
section Compare

/--
We say that `i ≤ j`, for two (canonical) id trees `i` and `j`, when the set
represented by `i` is a *subset* of the set represented by `j`.
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

/--
We say that `(i₁, e₁) ≤ (i₂, e₂)`, when either
`i₁` is a subset of `i₂` and `e₁` is less than or equal to `e₂`, or
`i₁` is a superset of `i₂` and `e₁` is strictly less than `e₂`.

That is, whether two clocks are *concurrent* (i.e. unrelated in the
happens-before relation) is determined by the id component of the clock.
Whenever two ids *are* related (in either direction), the event counter
disambiguates in which direction the clocks ought to be related.

Recall that a split will give disjoint subsets of its argument and keep the event
counter constant, which is why the first branch allows for the event counter to
be equal on both sides. A merge, on the other hand, gives a superset of its
arguments, but increments the event counter. Thus, when we see that `i₁` is a
superset of `i₂` we only relate the clocks if `e₂` has seen at least one more
merge than `e₁`.

TODO: I tweaked the definition below after writing the docstring, so
I should doublecheck the docs are still accurate
-/
instance : LE Clock where le c₁ c₂ :=
  -- Firstly, if `c₁` is a subset of (i.e, could have been split off from) `c₂`,
  -- then for `c₁` to have happened *before* `c₂`, it must have seen *stricty* more merges
  (c₁.i ≤ c₂.i ∧ c₁.e < c₂.e)
  -- Secondly, if `c₁` is a superset of `c₂`, then `c₁` cannot have been directly
  -- split of from `c₂` without having seen a merge in between, thus we say that
  -- `c₁` has happened before `c₂` if it has seen at least as many merges.
  ∨ (c₂.i ≤ c₁.i ∧ c₁.e ≤ c₂.e)

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

-- NOTE: we deliberatelyy put `le_iff` just before closing the namespace, as it
--       would otherwise cause divergence with the local `le_iff'` simp-lemma.
@[simp, grind =] theorem le_iff : (i.le j = true) ↔ (i ≤ j) := by
  simp [LE.le]

end CanonicalIdTree

/-! ### Clock LE lemmas -/
namespace Clock
variable {e : Nat}

@[grind =] theorem le_iff :
    c₁ ≤ c₂ ↔ ((c₁.i ≤ c₂.i ∧ c₁.e < c₂.e) ∨ (c₂.i ≤ c₁.i ∧ c₁.e ≤ c₂.e)) := by rfl

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

instance [DecidableLE α] : Decidable (x # y) := by unfold Unrelated; infer_instance

theorem unrel_symm : x # y ↔ y # x := by grind
theorem unrel_refl_iff : x # x ↔ ¬(x ≤ x) := by grind

end GenericUnrelLemmas

variable {i j : CanonicalIdTree} {c₁ c₂ : Clock}

/-! ### CanonicalIdTree Unrelated lemmas -/
namespace CanonicalIdTree

@[simp, grind .] theorem unrefl_irrefl : ¬(i # i) := by grind

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

/-- Two clocks are unrelated iff their id components are unrelated -/
@[simp, grind =] theorem unrel_iff : c₁ # c₂ ↔ c₁.i # c₂.i := by grind

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

theorem split_le : (split i).1 ≤ i ∧ (split i).2 ≤ i := by
  induction i using split.induct_unfolding <;> grind

@[simp, grind .] theorem split_fst_le : (split i).1 ≤ i := split_le.1
@[simp, grind .] theorem split_snd_le : (split i).2 ≤ i := split_le.2

theorem not_le_split (h : i ≠ zero) : ¬(i ≤ i.split.1) ∧ ¬(i ≤ i.split.2) := by
  induction i using split.induct_unfolding <;> grind

@[simp, grind .] theorem not_le_split_fst (h : i ≠ zero) : ¬(i ≤ i.split.1) := (not_le_split h).1
@[simp, grind .] theorem not_le_split_snd (h : i ≠ zero) : ¬(i ≤ i.split.2) := (not_le_split h).2

end SplitLemmas
end CanonicalIdTree

namespace Clock
def fork (id : Clock) : Clock × Clock :=
  let (i₁, i₂) := id.i.split
  (⟨i₁, id.e⟩, ⟨i₂, id.e⟩)

section ForkLemmas
variable (c c' : Clock)

@[simp, grind =] theorem i_fork_fst : c.fork.1.i = (c.i.split).1 := by rfl
@[simp, grind =] theorem i_fork_snd : c.fork.2.i = (c.i.split).2 := by rfl
@[simp, grind =] theorem e_fork_fst : c.fork.1.e = c.e := by rfl
@[simp, grind =] theorem e_fork_snd : c.fork.2.e = c.e := by rfl

/--
`c` happens-before both results of `c.fork`
-/
theorem le_fork : c ≤ c.fork.fst ∧ c ≤ c.fork.snd := by grind

/--
`c.fork.fst` is independent from `c.fork.snd`.
-/
theorem indep_fork : c.fork.fst # c.fork.snd := by
  sorry

variable {c c'} in
/--
If `c` is independent from `c'`, then the same holds for either result of `c.fork`.
-/
theorem indep_fork' (h : c # c') : c.fork.fst # c' ∧ c.fork.snd # c' := by
  sorry

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


namespace Clock
def join (c₁ : Clock) (c₂ : Clock) : Clock where
  i := .sum c₁.i c₂.i
  e := (max c₁.e c₂.e) + 1

section JoinLemmas
variable {c₁ c₂ c' : Clock}

@[simp, grind =] theorem i_join : (c₁.join c₂).i = c₁.i.sum c₂.i := by rfl
@[simp, grind =] theorem e_join : (c₁.join c₂).e = max c₁.e c₂.e + 1 := by rfl

/--
`c₁` and `c₂` both happen-before `c₁.join c₂`
-/
theorem le_join (c₁ c₂ : Clock) : c₁ ≤ c₁.join c₂ ∧ c₂ ≤ c₁.join c₂ := by grind

@[simp, grind .] theorem le_join_fst : c₁ ≤ c₁.join c₂ := (le_join c₁ c₂).1
@[simp, grind .] theorem le_join_snd : c₂ ≤ c₁.join c₂ := (le_join c₁ c₂).2

/--
If `c₁` and `c₂` are both independent from `c'`,
then the same holds for `c₁.join c₂`.
-/
theorem indep_join (h₁ : c₁ # c') (h₂ : c₂ # c') : c₁.join c₂ # c' := by
  -- TODO: finish proof
  sorry

end JoinLemmas
end Clock
end Join
