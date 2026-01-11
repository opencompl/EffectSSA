import EffectSSA.Assumptions.MemorySignature

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
  | store {t} (p : τ.Ptr) (x : τ.TVal t)
  /-- Location `p` was allocated, with type `t`. -/
  | alloc (t : τ.DType) (p : τ.Ptr)
  /-- Location `p` was freed -/
  | free (t : τ.DType) (p : τ.Ptr)
  | split

/-!
## Trace Definition
-/

inductive Trace where
  | seq : List (Event τ) → Trace
  | ub : Trace

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

end Trace
