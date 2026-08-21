module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.Notation.Refinement

namespace EffectSSA.ProofSketch
public section

class SSA (ι : Type) (σ : outParam Type) (ν : outParam Type) : Type where
  [decidableEq : DecidableEq ι]
  args : ι → VarSet
  results : ι → VarSet
  initialState : σ
  [stateRefine : Refinement σ]
  [valRefine : Refinement ν]

attribute [implicit_reducible, instance] SSA.stateRefine SSA.valRefine SSA.decidableEq

end
