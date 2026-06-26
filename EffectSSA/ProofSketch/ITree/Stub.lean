module

public import ITreeExtras
public import EffectSSA.ProofSketch.ITree.InterpM
public import EffectSSA.ProofSketch.ITree.HasEffect

/-!
# ITree Axioms
-/
@[expose] public section
namespace ITree.ITree



def forever : ITree ε α :=
  .tau <| forever
partial_fixpoint

@[simp]
axiom lift_forever [ε -< δ] : @lift ε δ α _ .forever = .forever
attribute [grind .] lift_forever
