module

public import ITreeExtras.Definition

/-!
# Basic (Missing) Definitions & Lemmas on ITrees
-/
@[expose] public section
namespace ITree.ITree
variable {t : ITree E R}

/-! Tag existing lemmas with grind -/
attribute [grind =] unfold_fold
                    tau_approx_1
                    vis_approx_1
                    tau_bind
                    LawfulMonad.bind_assoc
                    interp_pure
                    interp_tau

/-! ### `fold` and `unfold` -/
section Fold

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

end Fold

/-! ### `pure` (a.k.a. `ret`)-/
section Pure

@[simp, grind .]
theorem pure_eq_ret (x : α) :
  pure x = ret (E:=ε) x := by rfl

end Pure

/-! ### `bind` -/
section Bind

@[simp, grind =] theorem bind_ret : ret r >>= f = f r := by
  show pure r >>= f = _
  simp [-pure_eq_ret]

end Bind
