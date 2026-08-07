module

public import ITreeExtras.Bisim

/-!
# Refinement Relation
-/
public section
namespace EffectSSA.ProofSketch

class Refinement α where
  IsRefinedBy : α → α → Prop
  refl : ∀ x, IsRefinedBy x x := by grind
  trans : ∀ {x y z}, IsRefinedBy x y → IsRefinedBy y z → IsRefinedBy x z := by grind
export Refinement (IsRefinedBy)

infixl:50 " ⊒ " => IsRefinedBy

/-! ## Grind Annotations -/
section Grind

attribute [grind .] Refinement.refl
attribute [grind →] Refinement.trans

end Grind

/-! ## Trans -/
section Trans

instance [Refinement α] :
    Trans (· ⊒ · : α → α → _) (· ⊒ · : α → α → _) (· ⊒ · : α → α → _) where
  trans := Refinement.trans

end Trans

/-! ## Refinement Instances
We provide a refinement instance for `Option α`, where `none` is refined by
anything
-/
section Option

instance [Refinement α] : Refinement (Option α) where
  IsRefinedBy
    | none, _ => True
    | some _, none => False
    | some x, some y => x ⊒ y
  refl := by grind
  trans := by grind

end Option

section ITree
open ITree
variable {ε κ} [Effect ε κ]

instance [Refinement α] : Refinement (ITree ε α) where
  IsRefinedBy := ITree.BisimUpTo (· ⊒ ·)
  refl x := ITree.bisimUpTo_refl_of Refinement.refl x
  trans := by
    apply ITree.bisimUpTo_trans_of
    intro x y z
    exact Refinement.trans

end ITree
