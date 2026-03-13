import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Trace.Compat

/-!
# Memory Model Lawfulness

This file defines the extra properties that the memory model should adhere to,
to be considered lawful. This codifies:

* that once a trace is deemed illegal, adding more events to it should not make
    the trace legal again, and
* how `read` is expected to behave w.r.t. illegal traces and compatible events.

-/
namespace EffectSSA


/--

NOTE: we deliberately choose for the `Lawful` class to extend the base class,
rather than take it as an instance argument (as is more common). We don't really
care about working with non-lawful memory models, so the main development will
just assume lawfullness, even if not strictly necessary.
In return, this minimizes the boilerplate needed in each file.
-/
class LawfulMemoryModel τ extends MemoryModel τ where
  /--
  Adding more events to an illegal trace can only yield another illegal trace.
  -/
  cons_illegal_of_illegal {e} {es : Trace τ} : ¬es.Legal → ¬(e :> es).Legal
  /--
  Reading from an illegal trace should behave the same as reading from an UB
  trace (i.e., return some default value).
  -/
  read_illegal {es : Trace τ} (h : ¬es.Legal) :
    read t p es = read t p .ub

  /--
  Compatibility is symmetric
  -/
  compat_symm (e₁ e₂ : Event τ) : (e₁ ⌣ e₂) → (e₂ ⌣ e₁)

  /--
  If `e₁ ⌣ₑ e₂`, then the events can be added to a trace in either order
  without affecting subsequent reads of any location.
  -/
  read_eq_read (h : e₁ ⌣ e₂) (es : Trace τ) (t) (p) :
    read t p (e₁ :> e₂ :> es) = read t p (e₂ :> e₁ :> es)

  -- FIXME: I'm not sure, but we might also need something like the following
  --        to relate compatible states to legal traces. We'll see,
  --        for now I'll assume we don't and leave it out.
  -- /--
  -- If `e₁ ⌣ₑ e₂`, the events may be re-ordered without affecting legality of the
  -- trace.
  -- -/
  -- legal_iff_of_compat (h : e₁ ⌣ₑ e₂) (es : Trace τ) :
  --   (e₁ :> e₂ :> es).Legal ↔ (e₂ :> e₁ :> es)

  /--
  If `e ⌣ load p`, then adding `e` to any trace should not change the value
  read from location `p`.
  -/
  read_eq_read_of_load (h : e ⌣ (Event.load t p)) (es : Trace τ) :
    read t p (e :> es) = read t p es
