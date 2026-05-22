module

/-!
# Reduction Semantics
-/
public section
namespace EffectSSA.ProofSketch

/-! ## Reduce Class -/

class Reduce (α : Type) where
  ReducesTo : α → α → Prop
  /--
  For now, we assume that small-step reduction is deterministic.
  I'm not 100% sure we actually need this fact in the proof; it's here moreso
  because I'm not convinced I'll get the subtleties of the *statement* of
  contextual/denotational equivalence right in the presence of non-determinism.
  -/
  -- TODO: Eventually generalize this, and triple-check that the contextual and
  --   denotational equivalence statements still make sense when we do.
  eq_of_reducesTo_of_reducesTo : ∀ {x y z}, ReducesTo x y → ReducesTo x z → y = z := by grind

export Reduce (ReducesTo)
scoped infixl:50 " ⟹ " => ReducesTo

/-! ## Transitive Closure -/
section Closure

/--
`x ⟹+ y` holds when `x` reduces to `y` in one or more steps.

That is, `⟹+` is the transitive closure of `⟹`.
-/
inductive TReducesTo {α} [Reduce α] : α → α → Prop where
  | init {x y} : ReducesTo x y → TReducesTo x y
  | step {x y z} : ReducesTo x y → TReducesTo y z → TReducesTo x z
scoped infixl:arg " ⟹+ " => TReducesTo

class BReduce (α : Type) (β : outParam Type) extends Reduce α where
  /-- Type `β` can be seen as a subset of states in `α` which describe value. -/
  stateOfValue : β → α
  /-- Values ought to be terminal, i.e, may not reduce further. -/
  terminal_value : ∀ (b : β) (y : α), ¬(stateOfValue b ⟹ y) := by grind

@[grind] def BReducesTo {α β} [BReduce α β] : α → β → Prop :=
  fun x y => x ⟹+ (BReduce.stateOfValue y)
scoped infixl:50 " ⇓ " => BReducesTo

namespace TReducesTo
variable {α} [Reduce α] {x y z : α}

attribute [grind ., grind →] init

@[grind →] theorem trans : x ⟹+ y → y ⟹+ z → x ⟹+ z := by
  intro h₁ h₂
  induction h₁ <;> (
    apply TReducesTo.step
    · assumption
    · grind
  )

instance : Trans (α:=α) (· ⟹+ ·) (· ⟹+ ·) (· ⟹+ ·) where trans := by grind
instance : Trans (α:=α) (· ⟹+ ·) (· ⟹ ·) (· ⟹+ ·) where trans := by grind
instance : Trans (α:=α) (· ⟹ ·) (· ⟹+ ·) (· ⟹+ ·) where trans := by grind

end TReducesTo
end Closure
