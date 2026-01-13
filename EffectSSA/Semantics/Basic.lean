import EffectSSA.Assumptions.MemoryModel

/-!
# Basic Operation Semantics

This file defines the semantic functions for simple operations, which generally
just add a single event to a trace. These include:

* `load`
* `store`
* `alloc`
* `free`
* `split`

Note that these semantic functions will be used to describe both the implicit
and EffectSSA variations of each respective operation.
-/
namespace EffectSSA
variable {τ : Ty} [MemoryModel τ]

/--
`e :ℓ> es` adds an event `e` to a trace `es`, so long as the resulting trace
is considered legal. If the result would *not* be legal, return UB.
-/
def Trace.consLegal (e : Event τ) (es : Trace τ) : Trace τ :=
  let es := e :> es
  if es.Legal then es else .ub
@[inherit_doc] infixr:67 " :ℓ> " => Trace.consLegal

namespace Semantics

/--
Load a value of type `t` from the location pointed to by `p`,
assuming `es` describes all previous events.
-/
def load (t : τ.DType) (p : τ.Ptr) (es : Trace τ) : τ.DVal t × Trace τ :=
  (MemoryModel.read t p es, .load t p :ℓ> es)

/--
Store a value `x` of type `t` to the location pointed to by `p`,
assuming `es` describes all previous events.
-/
def store {t} (p : τ.Ptr) (x : τ.DVal t) (es : Trace τ) : Trace τ :=
  .store p x :ℓ> es

/--
Allocate the location `p` for a value of type `t`,
assuming `es` describes all previous events.
-/
def alloc (t : τ.DType) (p : τ.Ptr) (es : Trace τ) : Trace τ :=
  .alloc t p :ℓ> es

/--
Free the location `p`, which held a value of type `t`,
assuming `es` describes all previous events.
-/
def free (t : τ.DType) (p : τ.Ptr) (es : Trace τ) : Trace τ :=
  .free t p :ℓ> es

/--
Split effects, assuming `es` describes all previous events.
-/
def split (es : Trace τ) : Trace τ :=
  .split :ℓ> es
