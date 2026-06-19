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
namespace ITree

variable {E : Effect.{u}} {R : Type u}

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
  | ret {t1 t2 : ITree E R} {r : R} :
      t1 = .ret r → t2 = .ret r → Bisim t1 t2
  | tau {t1 t2 s1 s2 : ITree E R} :
      t1 = .tau s1 → t2 = .tau s2 → Bisim s1 s2 → Bisim t1 t2
  | vis {t1 t2 : ITree E R} {i : E.I} {k1 k2 : E.O i → ITree E R} :
      t1 = .vis i k1 → t2 = .vis i k2 →
      (∀ o : E.O i, Bisim (k1 o) (k2 o)) → Bisim t1 t2

/-- Bisimilar ITrees are equal. -/
theorem eq_of_bisim {t1 t2 : ITree E R} (h : Bisim t1 t2) : t1 = t2 := by
  have key : ∀ n (a b : ITree E R), Bisim a b → a.approx n = b.approx n := by
    intro n
    induction n
    · intros; rfl
    · intro a b hab
      cases hab
      <;> grind
  ext n
  exact key n t1 t2 h

end ITree
