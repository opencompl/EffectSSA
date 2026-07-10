module

public import ITreeExtras.Definition
public import ITreeExtras.Basic

/-!
# Strong Bisimulation of ITrees

`ITree.Bisim t1 t2` is the coinductive predicate for strong bisimilarity between
ITrees: both trees must take the same first step, including `tau`s, and all
continuations must again be bisimilar.

The main result is `ITree.eq_of_bisim`: bisimilarity implies equality.
-/

@[expose] public section
namespace ITree

variable {ε} {κ} [Effect.{u} ε κ] {α}

namespace ITree
variable {t : ITree ε α}

/--
Strong bisimilarity for ITrees.
Both trees must unfold to the same constructor, and continuations must again be bisimilar.
-/
coinductive Bisim {ε} {κ} [Effect.{u} ε κ] {α} :
    ITree ε α → ITree ε α → Prop where
  | ret : Bisim (.ret r) (.ret r)
  | tau : Bisim s₁ s₂ → Bisim (.tau s₁) (.tau s₂)
  | vis : (∀ o : κ i, Bisim (k₁ o) (k₂ o)) → Bisim (.vis i k₁) (.vis i k₂)

end ITree

-- Scope `≅` notation to top-level ITree namespace, rather than inner `ITree.ITree`
scoped infixl:arg " ≅ " => ITree.Bisim

namespace ITree

/-- Bisimilar ITrees are equal. -/
theorem eq_of_bisim {t₁ t₂ : ITree ε α} (h : t₁.Bisim t₂) : t₁ = t₂ := by
  ext n
  induction n generalizing t₁ t₂
  · rfl
  · cases h <;> grind

section Equiv

@[refl, simp, grind .]
theorem bisim_refl {ε} {κ} [Effect.{u} ε κ] {α} (x : ITree ε α) : x ≅ x := by
  apply Bisim.coinduct (· = ·)
  · rintro x _ rfl
    cases x
    case ret => simp
    case tau => simp
    case vis i k =>
      right; right
      refine ⟨i, k, k, ?_⟩
      simp
  · rfl
