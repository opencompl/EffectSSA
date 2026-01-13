import EffectSSA.Assumptions.MemorySignature

import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Operations

/-!

# Events & Traces

This file defines memory events, and traces of such events

-/
namespace EffectSSA
variable (τ : Ty) [MemorySignature τ]

/-!
## Event Definition
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
  | split
  deriving DecidableEq

/-!
## Trace Definition
-/

inductive Trace where
  | seq : List (Event τ) → Trace
  | ub : Trace
  deriving DecidableEq

/-!
### API
-/
variable {τ}

/-! ## Event API -/
namespace Event

/- An `Event` may be implicitly coerced to a `Trace`. -/
instance : Coe (Event τ) (Trace τ) where
  coe e := .seq [e]

end Event

/-! ## Trace API -/
namespace Trace

/- A list of `Event`s may be implicitly coerced to a `Trace`. -/
instance : Coe (List (Event τ)) (Trace τ) where
  coe := .seq

/--
Add a new event to the front of a trace,
where adding an event onto a UB trace just yields UB.

Written as `e :> ev`
-/
def cons (e : Event τ) : Trace τ → Trace τ
  | .seq ev => seq (e :: ev)
  | .ub => .ub
@[inherit_doc] infixr:67 " :> " => cons

/--
Append two traces.
-/
def append : Trace τ → Trace τ → Trace τ
  | .seq xs, .seq ys => .seq (xs ++ ys)
  | _, _ => .ub
instance : Append (Trace τ) where append := append

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


def events : Trace τ → Set (TraceZipper τ)
  | .ub => {}
  | .seq es => { ⟨es.take i, es[i], es.drop (i + 1)⟩ | (i : Fin es.length)}



end Trace
