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

/-! ## Refinement Instances -/
section Instances
variable [Refinement α]

/-! ### Option -/

/--
Refinement instance on `Option α`, where `none` is refined by anything,
and `some x` is refined by any `some y` s.t. `x ⊒ y`.
-/
instance : Refinement (Option α) where
  IsRefinedBy
    | none, _ => True
    | some _, none => False
    | some x, some y => x ⊒ y
  refl := by grind
  trans := by grind

/-! ### List -/
@[grind, grind cases]
inductive ListRefinement : List α → List α → Prop
  | nil : ListRefinement [] []
  | cons : x ⊒ y → ListRefinement xs ys → ListRefinement (x :: xs) (y :: ys)

/--
Refinement instance on `List α`,
where `xs` is refined by `ys` if they are of equal length and
each `x ∈ xs` is refined by the corresponding element `y` of `ys`.
-/
instance : Refinement (List α) where
  IsRefinedBy := ListRefinement
  refl xs := by induction xs <;> grind
  trans := @fun xs ys zs h₁ h₂ => by
    induction h₁ generalizing zs
    <;> cases h₂ <;> grind

/-! ### Unit
-/

/-- Trivial refinement instance on the unit type. -/
instance : Refinement PUnit.{u} where
  IsRefinedBy _ _ := True

@[simp, grind .]
theorem unit_isRefinedBy (u u' : PUnit.{u}) : u ⊒ u' := by grind

end Instances
