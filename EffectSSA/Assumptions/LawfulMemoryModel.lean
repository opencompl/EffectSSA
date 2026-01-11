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
