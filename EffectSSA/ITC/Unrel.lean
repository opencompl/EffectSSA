

/-!
# Unrel shorthand

We introduce `x # y` as a short-hand for `¬(x ≤ y) ∧ ¬(y ≤ x)`.
This notation will primarily be used when talking about clocks, although the
short-hand will be available on any type that implement `LE`.
-/
namespace EffectSSA.ITC
variable {α : Type u} [LE α]

/--
`x # y` is short for `¬(x ≤ y) ∧ ¬(y ≤ x)`

The preferred spelling in theorems is `unrel`
-/
@[grind] abbrev Unrel (x y : α) : Prop := ¬(x ≤ y) ∧ ¬(y ≤ x)
@[inherit_doc] infix:67 " # " => Unrel

/-!
## Lemmas
-/
namespace Unrel
variable (x y : α)

/-- `· # ·` is decidable when `· ≤ ·` is -/
instance [DecidableLE α] (x y : α) : Decidable (x # y) := by infer_instance

/-- `· # ·` is reflexive only when `· ≤ ·` is irreflexive. -/
@[grind =] theorem unrel_refl_iff : x # x ↔ ¬(x ≤ x) := by grind

end Unrel
