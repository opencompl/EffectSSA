import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Trace.Defs

/-!
# Memory Model


-/
namespace EffectSSA

/-!
## MemoryModel class
-/

class MemoryModel τ extends MemorySignature τ where
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

  /--
  `Compat` is a compatibility / non-interference relation between events,
  also written as `(· ⌣ₑ ·)`.
  Intuitively, two events are compatible if they may be freely reordered without
  changing the result of the events themselves (if either is a `load`) or any
  subsequent events.
  What this means precisely is formalized in `LawfulMemoryModel`.
  -/
  Compat : Event τ → Event τ → Prop
  [instDecideCompat : DecidableRel Compat]


/-! ## API -/
variable {τ} [μ : MemoryModel τ]

def Trace.Legal : Trace τ → Prop := MemoryModel.LegalTrace
instance : DecidablePred (@Trace.Legal τ _) :=
  μ.instDecideLegal

@[inherit_doc] infixl:60 " ⌣ₑ " => MemoryModel.Compat
attribute [instance] MemoryModel.instDecideCompat
