import EffectSSA.ITC.Unrel

/-!
# Interval Tree Clocks Stub

This file adds a collection of axioms, which will eventually be implemented in
https://github.com/opencompl/EffectSSA/pull/17.
-/
namespace EffectSSA.ITC

axiom Clock : Type

noncomputable section
namespace Clock

/-- A happens-before relation on clocks. -/
axiom le : Clock → Clock → Bool
instance : LE Clock where le x y := x.le y

/-- A clock can be (locally) split into two disjoint clocks. -/
axiom split : Clock → Clock × Clock

/-- Two clocks can be merged together into one. -/
axiom merge : Clock → Clock → Clock

/-- Equality of clocks is decidable -/
@[instance] axiom instDecidableEq : DecidableEq Clock

/-- An initial clock value, from which further clocks can be split. -/
axiom initial : Clock
instance : Inhabited Clock where default := initial

/-!
## Lemmas
-/
section Lemmas
variable (c c₁ c₂ c₃ : Clock)

/-!
### le
The happens-before relation (≤) is a preorder (reflexive and transitive).

It is not quite a partial order, as structurally distinct trees can represent
the same function space, and thus would be equivalent according to `≤`. That is,
without additional canonicity assumptions (beyond the normalization described in
the ITC paper), the relation is not quite anti-symmetric.
-/

@[refl, grind .] axiom le_refl : c ≤ c
@[grind →] axiom le_trans : c₁ ≤ c₂ → c₂ ≤ c₃ → c₁ ≤ c₃

instance : Std.IsPreorder Clock where
  le_refl := le_refl
  le_trans := le_trans

instance : DecidableLE Clock := fun c₁ c₂ =>
  decidable_of_bool (c₁.le c₂) (by rfl)

/-!
### Split
-/
section Split

/-!
`c` (strictly) happens-before both results of splitting `c`
-/
axiom le_split_fst : c ≤ c.split.fst
axiom le_split_snd : c ≤ c.split.snd

axiom not_split_fst_le : ¬(c.split.fst ≤ c)
axiom not_split_snd_le : ¬(c.split.snd ≤ c)

grind_pattern le_split_fst => _ ≤ c.split.fst
grind_pattern le_split_snd => _ ≤ c.split.snd

/-!
NOTE: the actual not_split_*_le are predicated on the id-component of the clock
being non-empty. That said, empty id component should never arise at the
top-level of the clock, and both split and merge preserve non-emptiness, so we
will bake in a top-level assumption of non-emptiness of the id in the Clock
structure to implement these axioms, without needing extra side-conditions.
-/

/--
The results of a `split` are independent.
-/
axiom indep_split : c.split.fst # c.split.snd

end Split

/-!
### Merge
-/
section Merge

/-!
`c₁` and `c₂` both happen-before the result of merging them.
-/
axiom left_le_merge  : c₁ ≤ c₁.merge c₂
axiom right_le_merge : c₂ ≤ c₁.merge c₂

grind_pattern left_le_merge => _ ≤ c₁.merge c₂
grind_pattern right_le_merge => _ ≤ c₁.merge c₂

/-!
`c₁` and `c₂` *strictly* happen-before the result their merger, if `c₁` and `c₂`
are independent.
-/
axiom not_merge_le_left  (h : c₁ # c₂) : ¬(c₁.merge c₂ ≤ c₁)
axiom not_merge_le_right (h : c₁ # c₂) : ¬(c₁.merge c₂ ≤ c₂)

end Merge
end Lemmas
