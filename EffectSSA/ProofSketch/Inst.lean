module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Assumptions

/-!
# Instructions

We assume some type `Inst` of instructions.

-/
public section
namespace EffectSSA.ProofSketch

/-- `Inst` is the type of instructions, with arguments and resulting variable binders. -/
structure Inst (ι : Type) where
  opCode : ι
  args : List VarId
  results : List VarId
  deriving DecidableEq

namespace Inst

/-! ### VarSet Views -/

noncomputable def argsSet (i : Inst ι) : VarSet := VarSet.setOf (· ∈ i.args)
noncomputable def resultsSet (i : Inst ι) : VarSet := VarSet.setOf (· ∈ i.results)

@[simp, grind =] theorem mem_argsSet {v : VarId} {i : Inst ι} :
    v ∈ i.argsSet ↔ v ∈ i.args := VarSet.mem_setOf

@[simp, grind =] theorem mem_resultsSet {v : VarId} {i : Inst ι} :
    v ∈ i.resultsSet ↔ v ∈ i.results := VarSet.mem_setOf

end Inst
