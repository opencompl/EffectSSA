module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Denote

namespace EffectSSA.ProofSketch

public class SSA (ι : Type) (σ : outParam Type) : Type where
  [decidableEq : DecidableEq ι]
  args : ι → VarSet
  results : ι → VarSet
