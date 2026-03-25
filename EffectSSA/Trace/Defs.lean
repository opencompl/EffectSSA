import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Assumptions.Compat
import EffectSSA.ITC

import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations

/-!

# Events & Traces

This file defines memory events, and traces of such events

-/
namespace EffectSSA
variable (τ : Ty) [MemorySignature τ]

open ITC (Clock)
noncomputable section -- TODO: #19 remove once ITC has been implemented
-- ^^ The following definitions use `Clock` axioms, and thus are noncomputable
--    untill we actually implement the Clock module.

/-!
## Event Definition
--------------------------------------------------------------------------------
-/

inductive Event where
  /-- A value of type `t` was loaded from location `p`. -/
  | load (t : τ.DType) (p : τ.Ptr)
  /-- The value `x` of type `t` was stored to location `p`. -/
  | store {t} (p : τ.Ptr) (x : τ.DVal t)
  /-- Location `p` was allocated, with type `t`. -/
  | alloc (t : τ.DType) (p : τ.Ptr)
  /-- Location `p` was freed -/
  | free (t : τ.DType) (p : τ.Ptr)
  deriving DecidableEq

/--
A `ClockedEvent τ c` is a `Event τ` tagged with some clock-value, which is
statically known to have happened before `c`.
-/
structure ClockedEvent (c : Clock) where
  clock : Clock
  event : Event τ
  clock_le : clock ≤ c := by grind
  deriving DecidableEq

/--
Two clocked events are compatible when either their clocks are ordered in either
direction (i.e, the events did not happen concurrently), or the underlying
events are compatible (i.e., the side-effects commute).
-/
instance [Compat (Event τ)] : HCompat (ClockedEvent τ c) (ClockedEvent τ c') where
  hCompat x y := x.clock # y.clock → x.event ⌣ y.event

/-!
## Trace Definition
--------------------------------------------------------------------------------
-/
variable [Compat (Event τ)]

structure Trace where
  /-- The current clock for the corresponding thread. -/
  clock : Clock
  events : List (ClockedEvent τ clock)
  /-- Whether UB has been raised. -/
  isUB : Bool
  /-- All events in a (non-UB) trace ought to be pairwise compatible. -/
  compat : ¬isUB → events.Pairwise (· ⌣ ·) := by solve | simp | grind
  deriving DecidableEq

/-!
## API
--------------------------------------------------------------------------------
-/
variable {τ}

/-! ### ClockedEvent API -/
namespace ClockedEvent

def cast_le (h : c ≤ c' := by grind) (e : ClockedEvent τ c) : ClockedEvent τ c' :=
  { e with clock_le := by grind [e.clock_le] }

end ClockedEvent

/-! ### Trace API -/
namespace Trace

/-- `∅` is the empty (non-UB) trace, without any events. -/
instance : EmptyCollection (Trace τ) where
  emptyCollection := { clock := .initial, events := [], isUB := false }

instance : Inhabited (Trace τ) where default := ∅

/--
The canonical UB trace.

Note that merging a trace with UB will always yield UB, so the precise clock
value of a trace with UB no longer matters.
-/
def ub : Trace τ where
  clock := .initial
  events := []
  isUB := true

/--
Add a new event to the front of a trace,
where adding an event onto a UB trace just yields UB.

The new event will be recorded with the current clock value stored in the trace.

Written as `e :> ev`
-/
def cons (e : Event τ) (es : Trace τ) : Trace τ :=
  let e := { clock := es.clock, event := e }
  { es with
    events := e :: es.events
    compat := by
      have (e' : ClockedEvent τ es.clock) : e ⌣ e' := by
        intro hc
        have : e.clock = es.clock := rfl
        have := e'.clock_le
        grind
      intro hUB
      simp [es.compat hUB, this]
  }
@[inherit_doc] infixr:67 " :> " => cons

/--
A `TraceZipper` points to a specific event in a (non-UB) trace, while also
storing a list of all events that happend before and after.

NOTE: Although this type is called a zipper, the chronological ordering of
events in `pre` and `post` is the same.

FIXME: Should this be renamed to something other than zipper to avoid confusion?
FIXME: The namespace is duplicated in Trace.TraceZipper, should I find another name
        and/or define it outside the Trace namespace? The name is not super
       relevant, as I'm unlikely to explicitly name it much
       outside of this file.
-/
structure TraceZipper τ [MemorySignature τ] where
  /-- Events which happened *after* `event`. -/
  pre : List (Event τ)
  /-- The main event of interest. -/
  event : Event τ
  /-- Events which happened *before* `event`. -/
  post : List (Event τ)

-- FIXME: the naming `pre`/`post` is correct in the sense they are pre/postfixes
--   of the trace, but have the wrong chronological implication!


def eventSet (es : Trace τ) : Set (TraceZipper τ) :=
  if !es.isUB then
    let ev := es.events.map (·.event)
    { ⟨ev.take i, ev[i], ev.drop (i + 1)⟩ | (i : Fin ev.length)}
  else
    ∅

end Trace

/-
## Basic Lemmas
--------------------------------------------------------------------------------

Lemmas needed to prove invariants for further definitions.
-/

namespace ClockedEvent
variable (x : ClockedEvent τ c₁) (y : ClockedEvent τ c₂)

@[grind =] theorem compat_iff : x ⌣ y ↔ (x.clock # y.clock → x.event ⌣ y.event) := by rfl

@[simp, grind =] theorem cast_le_compat (h : c₁ ≤ c₁') :
    x.cast_le h ⌣ y ↔ x ⌣ y := by
  grind [cast_le]

@[simp, grind =] theorem compat_cast_le (h : c₂ ≤ c₂') :
    x ⌣ y.cast_le h ↔ x ⌣ y := by
  grind [cast_le]

@[grind =>] theorem compat_of_not_unrel (h : ¬(x.clock # y.clock)) : x ⌣ y := by grind

end ClockedEvent
