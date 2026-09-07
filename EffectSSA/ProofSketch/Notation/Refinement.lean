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
namespace Option

/--
Refinement instance on `Option α`, where `none` is refined by anything,
and `some x` is refined by any `some y` s.t. `x ⊒ y`.
-/
instance : Refinement (Option α) where
  IsRefinedBy x? y? :=
    (hx : x?.isSome) → ∃ hy : y?.isSome, x?.get hx ⊒ y?.get hy
  refl := by grind
  trans := by grind

@[grind =] theorem isRefinedBy_iff {x? y? : Option α} :
    x? ⊒ y? ↔ (hx : x?.isSome) → ∃ hy : y?.isSome, x?.get hx ⊒ y?.get hy := by rfl

@[simp, grind .] theorem none_isRefinedBy (x : Option α) : (none : Option α) ⊒ x := by simp [(· ⊒ ·)]
@[simp, grind .] theorem not_some_isRefinedBy_none {x : α} :
    ¬(some x) ⊒ none := by simp [(· ⊒ ·)]
@[simp, grind =] theorem some_isRefinedBy_some {x y : α} :
    (some x) ⊒ (some y) ↔ x ⊒ y := by simp [(· ⊒ ·)]

end Option

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


@[simp, grind =] theorem List.cons_isRefinedBy_cons {x y : α} {xs ys : List α} :
  (x :: xs) ⊒ (y :: ys) ↔ x ⊒ y ∧ xs ⊒ ys := by
  constructor
  · rintro ⟨_⟩; and_intros <;> assumption
  · exact fun ⟨hx, hxs⟩ => ListRefinement.cons hx hxs

theorem List.mapM_isRefinedBy_congr (xs : List β) {f g : β → Option α} :
    (∀ x ∈ xs, f x ⊒ g x) → xs.mapM f ⊒ xs.mapM g := by
  -- **AI DISCLOSURE**: LLM-generated proof
  intro hx
  induction xs with
  | nil => exact Refinement.refl _
  | cons x xs ih =>
    have hxx := hx x (by simp)
    specialize ih (fun v hv => hx v (by simp [hv]))
    simp only [List.mapM_cons, Option.bind_eq_bind]
    cases hfx : f x
    · simp
    · cases hgx : g x <;> rw [hfx, hgx] at hxx
      · simp at hxx
      · simp only [Option.some_isRefinedBy_some] at hxx
        simp only [Option.bind_some]
        cases hxsf : xs.mapM f <;> cases hxsg : xs.mapM g <;> rw [hxsf, hxsg] at ih
        <;> grind

/-! ### Unit -/

/-- Trivial refinement instance on the unit type. -/
instance : Refinement PUnit.{u} where
  IsRefinedBy _ _ := True

@[simp, grind .]
theorem unit_isRefinedBy (u u' : PUnit.{u}) : u ⊒ u' := by grind

/-! ### Fallback -/

/--
Default refinement instance for any type, where `x` is only refined by itself.

Marked low-priority such that specific types may provide a better refinement
instance, if available.
-/
instance (priority := low) : Refinement α where
  IsRefinedBy x y := x = y

end Instances
