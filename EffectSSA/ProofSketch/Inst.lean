module

public import EffectSSA.ProofSketch.VarSet

/-!
# Instructions

We assume some type `Inst` of instructions.

-/
public section
namespace EffectSSA.ProofSketch

/-- `Inst` is the type of instructions. -/
axiom Inst : Type


namespace Inst


/-!
## Variables
-/
section Vars

/-- `i.args` is the set of arguments of instruction `i`. -/
axiom args : Inst → VarSet

/-- `i.results` is the set of results of instruction `i`. -/
axiom results : Inst → VarSet

end Vars
end Inst
