module

public import ITreeExtras.Definition

/-!
# Basic (Missing) Definitions & Lemmas on ITrees
-/
@[expose] public section
namespace ITree.ITree
variable {ε} {κ} [Effect.{u} ε κ] {α} {t : ITree ε α}

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
theorem fold_unfold (t : ITreeF ε α _) :
    (fold t).unfold = t := by
  simp [ITree.fold, ITree.unfold]

@[grind =] theorem unfold_eq_ret_iff :
    t.unfold = .ret x ↔ t = .ret x := by
  grind [ret]

@[grind =] theorem unfold_eq_tau_iff :
    t.unfold = .tau t' ↔ t = .tau t' := by
  grind [tau]

@[grind =] theorem unfold_eq_vis_iff :
    t.unfold = .vis e k ↔ t = .vis e k := by
  grind [vis]

end Fold

/-! ### "No Confusion" lemmas -/
section NoConfusion

@[simp, grind .] theorem tau_neq_ret {t : ITree ε α} {x : α} : tau t ≠ ret x := by
  intro h; have := congrArg unfold h; simp at this

@[simp, grind .] theorem tau_neq_vis {t : ITree ε α} {i : ε.I}
    {k : ε.O i → ITree ε α} : tau t ≠ vis i k := by
  intro h; have := congrArg unfold h; simp at this

@[simp, grind .] theorem ret_neq_vis {x : α} {i : ε.I}
    {k : ε.O i → ITree ε α} : ret x ≠ vis i k := by
  intro h; have := congrArg unfold h; simp at this

end NoConfusion

/-! ### Injectivity lemmas -/
section Inj

@[grind .] theorem vis_inj {i₁ i₂ : ε.I}
    {k₁ : ε.O i₁ → ITree ε α} {k₂ : ε.O i₂ → ITree ε α}
    (h : vis i₁ k₁ = vis i₂ k₂) :
    i₁ = i₂ ∧ k₁ ≍ k₂ := by
  have hu := congrArg unfold h
  simpa only [unfold_vis, ITreeF.vis.injEq] using hu

@[grind .] theorem ret_inj {x y : α} (h : @ret ε α x = ret y) : x = y := by
  have hu := congrArg unfold h
  simpa only [unfold_ret, ITreeF.ret.injEq] using hu

end Inj

/-! ### `pure` (a.k.a. `ret`)-/
section Pure

@[simp, grind .]
theorem pure_eq_ret (x : α) :
  pure x = ret (ε:=ε) x := by rfl

end Pure

/-! ### `bind` -/
section Bind

@[simp, grind =] theorem bind_ret : ret (ε:=ε) r >>= f = f r := by
  show pure r >>= f = _
  simp [-pure_eq_ret]

end Bind
