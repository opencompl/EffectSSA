/-!
# Theorems about List

-/
namespace List
variable {R : α → α → Prop} [Std.Refl R] [Std.Symm R]

/--
If a relation `R` is reflexive and symmetric, then `xs.pairwise R` implies
that any two elements of `xs` are related in `R`.
-/
theorem rel_of_pairwise {xs : List α} (h : xs.Pairwise R) {x₁ x₂} :
    x₁ ∈ xs → x₂ ∈ xs → R x₁ x₂ := by
  induction h
  case nil => grind
  case cons x xs h₁ h₂ ih =>
    simp only [mem_cons]
    rintro (rfl|hx₁) (rfl|hx₂)
    <;> grind [Std.Refl, Std.Symm]
