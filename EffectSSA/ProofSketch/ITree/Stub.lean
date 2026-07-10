module

public import ITreeExtras
public import EffectSSA.ProofSketch.ITree.InterpM

/-!
# ITree Axioms
-/
@[expose] public section
namespace ITree.ITree
variable {ε} {κ : ε → Type _} [Effect ε κ] {α : Type _}

def forever : ITree ε α :=
  .tau <| forever
partial_fixpoint

@[simp]
axiom lift_forever
    {ε δ} {κ₁ : ε → Type _} {κ₂ : δ → Type _}
    [Effect ε κ₁] [Effect δ κ₂] [ε -< δ] {α : Type _} :
    (liftM (n:=ITree δ) (forever (ε:=ε) (α:=α))) = forever
attribute [grind .] lift_forever
