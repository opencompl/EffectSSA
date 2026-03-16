import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Assumptions.Compat
import EffectSSA.Trace.Defs

/-!
# Memory Model


-/
namespace EffectSSA

/-!
## MemoryModel class
-/

/--
The `MemoryModel` of `τ` gives (1) a semantics to the `read` operation, (2) a
notion of compatibility of (memory) events, and (3) a notion of which traces of
events are legal.

Intuitively, two events ought to be compatible if they may be freely reordered
without changing the result of the events themselves (e.g., when either is a
`load`) or any subsequent events. In other words, the events ought to be
compatible iff their effects commute.
-/
class MemoryModel τ extends MemorySignature τ, Compat (Event τ) where
  /--
  `read ty p ev` should return the value (of type `ty`) stored at location `p`,
  given a trace of previous events `ev`.

  If this read is illegal, `read` may return an arbitrary value.
  -/
  read : (t : τ.DType) → τ.Ptr → Trace τ → τ.DVal t

  /--
  `LegalTrace` is a (decidable) predicate to identify which traces of events are
  deemed legal by the memory model.
  Illegal traces are considered equivalent to UB.

  This is the main mechanism to define that, e.g., an out-of-bounds `load` is
  UB, by excluding any trace with an the out-of-bounds `load` event from the
  `LegalTrace` predicate.
  -/
  LegalTrace : Trace τ → Prop
  [instDecideLegal : DecidablePred LegalTrace]
  /-- Compatibility of events should be decidable. -/
  [instDecideCompat : DecidableCompat (Event τ)]


/-! ## API -/
variable {τ} [μ : MemoryModel τ]

def Trace.Legal : Trace τ → Prop := MemoryModel.LegalTrace
instance : DecidablePred (@Trace.Legal τ _) :=
  μ.instDecideLegal

attribute [reducible, instance] MemoryModel.instDecideCompat
