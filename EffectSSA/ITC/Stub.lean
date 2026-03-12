import EffectSSA.ITC.Unrel

/-!
# Interval Tree Clocks Stub

This file adds a collection of axioms, which will eventually be implemented in
https://github.com/opencompl/EffectSSA/pull/17.
-/
namespace EffectSSA.ITC

axiom Clock : Type

namespace Clock

/-- A happens-before relation on clocks. -/
axiom le : Clock → Clock → Bool
instance : LE Clock where le x y := x.le y

/-- A clock can be (locally) split into two disjoint clocks. -/
axiom split : Clock → Clock × Clock

/-- Two clocks can be merged together into one. -/
axiom merge : Clock → Clock → Clock

/-!
## Lemmas
-/
section Lemmas
variable (c c₁ c₂ : Clock)

/-!
### Split
-/
section Split

/-!
`c` (strictly) happens-before both results of splitting `c`
-/
axiom le_split_snd : c ≤ c.split.snd
axiom le_split_fst : c ≤ c.split.fst

axiom not_split_fst_le : ¬(c.split.fst ≤ c)
axiom not_split_snd_le : ¬(c.split.snd ≤ c)

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

/-!
`c₁` and `c₂` *strictly* happen-before the result their merger, if `c₁` and `c₂`
are independent.
-/
axiom not_merge_le_left  (h : c₁ # c₂) : ¬(c₁.merge c₂ ≤ c₁)
axiom not_merge_le_right (h : c₁ # c₂) : ¬(c₁.merge c₂ ≤ c₂)

end Merge
end Lemmas
