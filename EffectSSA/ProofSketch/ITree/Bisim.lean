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

/--
Strong bisimilarity for ITrees.
Both trees must unfold to the same constructor, and continuations must again be bisimilar.
-/
coinductive Bisim : ITree E R → ITree E R → Prop where
  | ret {t1 t2 : ITree E R} {r : R} :
      t1.unfold = .ret r → t2.unfold = .ret r → Bisim t1 t2
  | tau {t1 t2 s1 s2 : ITree E R} :
      t1.unfold = .tau s1 → t2.unfold = .tau s2 → Bisim s1 s2 → Bisim t1 t2
  | vis {t1 t2 : ITree E R} {i : E.I} {k1 k2 : E.O i → ITree E R} :
      t1.unfold = .vis i k1 → t2.unfold = .vis i k2 →
      (∀ o : E.O i, Bisim (k1 o) (k2 o)) → Bisim t1 t2

/-- Bisimilar ITrees are equal. -/
theorem eq_of_bisim {t1 t2 : ITree E R} (h : Bisim t1 t2) : t1 = t2 := by
  have key : ∀ n (a b : ITree E R), Bisim a b → a.approx n = b.approx n := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro a b hab
      cases hab with
      | ret h1 h2 =>
          rename_i r
          have ha : a = .ret r := by have h := ITree.unfold_fold a; rw [h1] at h; exact h.symm
          have hb : b = .ret r := by have h := ITree.unfold_fold b; rw [h2] at h; exact h.symm
          simp [ha, hb]
      | tau h1 h2 hc =>
          rename_i s1 s2
          have ha : a = .tau s1 := by have h := ITree.unfold_fold a; rw [h1] at h; exact h.symm
          have hb : b = .tau s2 := by have h := ITree.unfold_fold b; rw [h2] at h; exact h.symm
          simp only [ha, hb, tau_approx_1, ih s1 s2 hc]
      | vis h1 h2 hc =>
          rename_i i k1 k2
          have ha : a = .vis i k1 := by have h := ITree.unfold_fold a; rw [h1] at h; exact h.symm
          have hb : b = .vis i k2 := by have h := ITree.unfold_fold b; rw [h2] at h; exact h.symm
          simp only [ha, hb, vis_approx_1]
          congr 1
          funext o
          exact ih (k1 o) (k2 o) (hc o)
  ext n
  exact key n t1 t2 h

end ITree
