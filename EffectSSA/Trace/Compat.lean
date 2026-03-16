import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Trace.Defs

/-!
# Trace Compatibility

This file lifts the event compatibility relation from the `MemoryModel` class
into a compatibility relation on traces, and defines `· ⌣ ·` as notation for
trace compatibility. That said, a coercion from events to traces exists, so
`· ⌣ ·` can be used with single events also.

-/
namespace EffectSSA
variable {τ} [MemoryModel τ]

noncomputable section
-- TODO: #19 make computable once ITC is implemented

/--
Two traces are compatible when they are legal to merge, which is exactly when
the event are pairwise either ordered by their clocks, or the side effects are
compatible (i.e, they are compatible as `ClockedEvent`s).

Note that a trace with UB is not compatible with anything.
-/

structure Trace.Compat (es : Trace τ) (ds : Trace τ) : Prop where
  ub_left : ¬es.isUB
  ub_right : ¬ds.isUB
  /-- All pairs of clocked events need to pairwise compatible -/
  events : ∀ e ∈ es.events, ∀ d ∈ ds.events, e ⌣ d
instance : Compat (Trace τ) where compat := Trace.Compat

/-!
## Decidability
Compatibility of both ClockedEvents and Traces is decidable.
-/

instance [DecidableCompat (Event τ)] : DecidableHCompat (ClockedEvent τ c₁) (ClockedEvent τ c₂) :=
  fun x y => decidable_of_iff' _ (ClockedEvent.compat_iff x y)

@[grind =] theorem Trace.compat_iff {es ds : Trace τ} :
    es ⌣ ds ↔ ¬es.isUB ∧ ¬ds.isUB ∧ (∀ e ∈ es.events, ∀ d ∈ ds.events, e ⌣ d) := by
  show es.Compat ds ↔ _
  grind [Trace.Compat]

instance [DecidableCompat (Event τ)] : DecidableCompat (Trace τ) := fun _es _ds =>
  decidable_of_iff' _ Trace.compat_iff

/-!
## ClockedEvent Compatibility
-/
namespace ClockedEvent
variable (e₁ : ClockedEvent τ c₁) (e₂ : ClockedEvent τ c₂)

/--
Compatibility of clocked events is symmetric, when compatibility of events is.
-/
@[symm] theorem compat_symm [SymmCompat (Event τ)] : e₁ ⌣ e₂ → e₂ ⌣ e₁ := by
  grind [SymmCompat.symm (α := Event τ)]
