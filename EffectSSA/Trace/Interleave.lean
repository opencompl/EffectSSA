import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Trace.Defs

import Mathlib.Data.Set.Defs

/-!
# Trace Interleavings

This file defines `· ∥ ·`, the set of all possible interleavings of the events
from two traces.
-/
namespace EffectSSA

namespace Trace
variable {τ} [MemorySignature τ]

/-! ## interleave -/

/--
`IsInterleaving is xs ys` holds when `is` is a valid interleaving of the
events of traces `xs` and `ys` (while maintaining the ordering between events
from the same trace).

This is an auxiliary definition, the preferred spelling is `is ∈ (xs ∥ ys)`.

Note that this assumes the traces are not UB, i.e.: `UB ∥ _ = _ ∥ UB = ∅`
-/
inductive IsInterleaving : Trace τ → Trace τ → Trace τ → Prop where
  | nil : IsInterleaving ys (.seq []) ys
  | event (xs₁ xs₂) :
      xs = xs₁ ++ xs₂ →
      ------------------------------------------
      IsInterleaving (xs₁ ++ (e :> xs₂)) e ys
  | cons :
      IsInterleaving is (.seq (d :: xs)) ys →
      IsInterleaving ks (.seq [e]) is →
      ------------------------------------------
      IsInterleaving ks (.seq (e :: d :: xs)) ys

def interleave (xs ys : Trace τ) : Set (Trace τ) :=
  { is | is.IsInterleaving xs ys }
infix:60 " ∥ " => interleave


end Trace
