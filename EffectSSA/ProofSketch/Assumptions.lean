module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.Notation.Refinement

namespace EffectSSA.ProofSketch
public section

class SSA (ι : Type) (σ : outParam Type) (ν : outParam Type) : Type where
  [decidableEq : DecidableEq ι]
  [instDenote : Denote ι (σ → List ν → σ × List ν)]
  initialState : σ
  [stateRefine : Refinement σ]
  [valRefine : Refinement ν]

attribute [implicit_reducible, instance]
  SSA.stateRefine SSA.valRefine SSA.decidableEq SSA.instDenote

/-!
## Axiomatized SSA Instance
-/

axiom OpCode : Type

/-- The type of runtime values. -/
axiom Val : Type

/-- The type of global runtime state (e.g., memory). -/
axiom State : Type

/-- `SSA` instance for the concrete `Inst` type. -/
@[instance] axiom instSSA : SSA OpCode State Val

end
