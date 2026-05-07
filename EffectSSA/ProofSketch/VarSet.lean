module

import Mathlib.Data.Set.Basic

/-!
# VarSet
-/
namespace EffectSSA.ProofSketch

/-- `Var` is the type of variables -/
public axiom Var : Type

/-- `VarSet` is a set of variables. -/
public def VarSet := Set Var

namespace VarSet

end VarSet
