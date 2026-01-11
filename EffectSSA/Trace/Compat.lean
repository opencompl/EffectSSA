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

inductive Compat : Trace τ → Trace τ → Prop
  | seq :
      (∀ x ∈ xs, ∀ y ∈ ys, MemoryModel.Compat x y)
      → Trace.Compat (.seq xs) (.seq ys)

-- N.B: Should UB be compatible with everything, or with nothing?
-- I don't think it actually matters, as merging incompatible traces simply
-- yields UB, but if UB was deemed compatible, then appending the other trace
-- to UB still just yields UB. Thus, I'll say that UB is *NOT* compatible with
-- anything, since that's the shorter definition.

infixl:60 " ⌣ " => Compat

end Trace
