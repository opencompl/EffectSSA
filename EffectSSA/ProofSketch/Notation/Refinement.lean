module

/-!
# Refinement Relation
-/
public section
namespace EffectSSA.ProofSketch

class Refinement α where
  IsRefinedBy : α → α → Prop
  refl : ∀ x, IsRefinedBy x x := by grind
  trans : ∀ {x y z}, IsRefinedBy x y → IsRefinedBy y z → IsRefinedBy x z := by grind
  antisymm : ∀ {x y}, IsRefinedBy x y → IsRefinedBy y x → x = y := by grind
export Refinement (IsRefinedBy)

infixl:50 " ⊑ " => IsRefinedBy

/-! ## Grind Annotations -/
section Grind

attribute [grind .] Refinement.refl
attribute [grind .] Refinement.antisymm
attribute [grind →] Refinement.trans

end Grind

/-! ## Trans -/
section Trans

instance [Refinement α] :
    Trans (· ⊑ · : α → α → _) (· ⊑ · : α → α → _) (· ⊑ · : α → α → _) where
  trans := Refinement.trans

end Trans

/-! ## Refinement Option Instance
We provide a refinement instance for `Option α`, where `none` is refined by
anything
-/
section Option

instance [Refinement α] : Refinement (Option α) where
  IsRefinedBy
    | none, _ => True
    | some _, none => False
    | some x, some y => x ⊑ y
  refl := by grind
  trans := by grind
  antisymm := by grind

end Option
