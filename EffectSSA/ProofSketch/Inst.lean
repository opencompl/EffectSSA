module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Effect

public import ITreeExtras.HasEffect

/-!
# Instructions

We assume some type `Inst` of instructions.

-/
public section
namespace EffectSSA.ProofSketch

namespace Inst

@[instance] axiom decideEq : DecidableEq Inst

/-!
## Variables
-/
section Vars
open LocalEff

/--
We say that instruction `i` defines variable `x`, if *any* trace of its interpretation
(`handleInst i`) has a `(push x _)` side effect.
-/
def Defines (i : Inst) (x : VarId) : Prop :=
  ∃ a, (handleInst i).HasEffect (push x a)

/--
We say that instruction `i` reads variable `x`, if *any* trace of its interpretation
(`handleInst i`) has a `(read x)` side effect.
-/
def Reads (i : Inst) (x : VarId) : Prop :=
  (handleInst i).HasEffect (read x)

/-- `i.args` is the set of arguments of instruction `i`. -/
axiom args : Inst → VarSet

/-- `i.results` is the set of results of instruction `i`. -/
axiom results : Inst → VarSet

end Vars
end Inst
