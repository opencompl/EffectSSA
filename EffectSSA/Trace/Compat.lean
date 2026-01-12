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

namespace Trace

/--
Compatibility relation on traces, written as `es ⌣ ds`

Two traces are compatible if their events are pairwise compatible according
to the memory model. Undefined behavior (UB) is not compatible with anything.
-/
inductive Compat : Trace τ → Trace τ → Prop
  | seq :
      (∀ x ∈ xs, ∀ y ∈ ys, x ⌣ₑ y)
      → Trace.Compat (.seq xs) (.seq ys)
infixl:60 " ⌣ " => Compat

/-!
Compatibility is decidable.
-/
section Decide

theorem seq_compat_seq_iff {xs ys : List (Event τ)} :
    (.seq xs ⌣ .seq ys) ↔ ∀ x ∈ xs, ∀ y ∈ ys, x ⌣ₑ y :=
  ⟨fun (Compat.seq h) => h, Compat.seq⟩

instance : DecidableRel (@Compat τ _)
  | .seq _, .seq _ => decidable_of_iff _ seq_compat_seq_iff.symm
  | .ub, _ | _, .ub => .isFalse (by rintro ⟨⟩)

end Decide




end Trace
