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
  /-- Compatibility of events should be symmetric. -/
  [instSymmCompat : Std.Symm (· ⌣ · : Event τ → Event τ → _)]


/-! ## API -/
variable {τ} [μ : MemoryModel τ]

def Trace.Legal : Trace τ → Prop := MemoryModel.LegalTrace
instance : DecidablePred (@Trace.Legal τ _) :=
  μ.instDecideLegal

attribute [reducible, instance] MemoryModel.instDecideCompat
attribute [instance] MemoryModel.instSymmCompat
