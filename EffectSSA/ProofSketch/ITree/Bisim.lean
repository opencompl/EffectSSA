module

public import ITree.Definition

/-!
# Strong Bisimulation of ITrees

`ITree.Bisim t1 t2` is the coinductive predicate for strong bisimilarity between
ITrees: both trees must take the same first step, including `tau`s, and all
continuations must again be bisimilar.

The main result is `ITree.eq_of_bisim`: bisimilarity implies equality.
-/

@[expose] public section
namespace ITree

variable {E : Effect.{u}} {R : Type u}

namespace ITree
section Upstream
attribute [grind =] unfold_fold tau_approx_1 vis_approx_1
variable {t : ITree E R}

-- TODO: this lemma ought to be called `unfold_fold`, but that lemma already exists
--       (and was misnamed; it ought to be called `fold_unfold`).
@[simp, grind =]
theorem fold_unfold (t : ITreeF E R _) :
    (fold t).unfold = t := by
  simp [ITree.fold, ITree.unfold]

@[grind =] theorem of_unfold_eq_ret :
    t.unfold = .ret x ↔ t = .ret x := by
  grind [ret]

@[grind =] theorem of_unfold_eq_tau :
    t.unfold = .tau t' ↔ t = .tau t' := by
  grind [tau]

@[grind =] theorem of_unfold_eq_vis :
    t.unfold = .vis e k ↔ t = .vis e k := by
  grind [vis]

end Upstream

/--
Strong bisimilarity for ITrees.
Both trees must unfold to the same constructor, and continuations must again be bisimilar.
-/
coinductive Bisim : ITree E R → ITree E R → Prop where
  | ret : Bisim (.ret r) (.ret r)
  | tau : Bisim s₁ s₂ → Bisim (.tau s₁) (.tau s₂)
  | vis : (∀ o : E.O i, Bisim (k₁ o) (k₂ o)) → Bisim (.vis i k₁) (.vis i k₂)

end ITree

-- Scope `≅` notation to top-level ITree namespace, rather than inner `ITree.ITree`
scoped infixl:arg " ≅ " => ITree.Bisim

namespace ITree

/-- Bisimilar ITrees are equal. -/
theorem eq_of_bisim {t₁ t₂ : ITree E R} (h : t₁.Bisim t₂) : t₁ = t₂ := by
  ext n
  induction n generalizing t₁ t₂
  · rfl
  · cases h <;> grind
