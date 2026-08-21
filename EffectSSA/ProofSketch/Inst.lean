module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Assumptions

/-!
# Instructions

We assume some type `Inst` of instructions.

-/
public section
namespace EffectSSA.ProofSketch

/-- `Inst` is the type of instructions. -/
axiom Inst : Type

namespace Inst

@[instance] axiom decideEq : DecidableEq Inst

/-!
## Variables
-/
section Vars

/-- `i.args` is the set of arguments of instruction `i`. -/
axiom args : Inst → VarSet

/-- `i.results` is the set of results of instruction `i`. -/
axiom results : Inst → VarSet

end Vars

/-!
## SSA Instance
-/

/-- The type of runtime values. -/
axiom Val : Type

/-- The type of global runtime state (e.g., memory). -/
axiom State : Type

/-- `SSA` instance for the concrete `Inst` type. -/
@[instance] axiom instSSA : SSA Inst State Val

end Inst
