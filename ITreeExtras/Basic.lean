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
                    vis_bind
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

@[simp, grind =] theorem vis_inj {i₁ i₂ : ε.I}
    {k₁ : ε.O i₁ → ITree ε α} {k₂ : ε.O i₂ → ITree ε α} :
    vis i₁ k₁ = vis i₂ k₂ ↔ i₁ = i₂ ∧ k₁ ≍ k₂ := by
  constructor
  · intro h; have hu := congrArg unfold h; simpa only [unfold_vis, ITreeF.vis.injEq] using hu
  · rintro ⟨rfl, rfl⟩; rfl

@[simp, grind =] theorem tau_inj {t₁ t₂ : ITree ε α} : tau t₁ = tau t₂ ↔ t₁ = t₂ := by
  constructor
  · intro h; have hu := congrArg unfold h; simpa only [unfold_tau, ITreeF.tau.injEq] using hu
  · rintro rfl; rfl

@[simp, grind =] theorem ret_inj {x y : α} : @ret ε α x = ret y ↔ x = y := by
  constructor
  · intro h; have hu := congrArg unfold h; simpa only [unfold_ret, ITreeF.ret.injEq] using hu
  · rintro rfl; rfl

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

@[grind =]
theorem bind_eq_ret_iff (t : ITree ε α) (f : α → ITree ε β) (x) :
    t >>= f = ret x ↔ ∃ r, t = ret r ∧ f r = ret x := by
  cases t <;> grind

@[grind =]
theorem bind_eq_tau_iff (t : ITree ε α) (f : α → ITree ε β) (t'') :
    t >>= f = tau t'' ↔
      (∃ r, t = ret r ∧ f r = tau t'')
      ∨ (∃ t', t = tau t' ∧ t'' = t' >>= f) := by
  cases t <;> grind

@[grind =]
theorem bind_eq_vis_iff (t : ITree ε α) (f : α → ITree ε β) (i) (k) :
    t >>= f = vis i k ↔
      (∃ x, t = ret x ∧ f x = vis i k)
      ∨ (∃ k', t = vis i k' ∧ k = fun o => k' o >>= f) := by
  cases t with
  | ret r =>
    rw [pure_bind]
    refine ⟨fun h => .inl ⟨r, rfl, h⟩, ?_⟩
    rintro (⟨w, hw, hf⟩ | ⟨w, h, _⟩)
    · obtain rfl : r = w := by simp_all
      exact hf
    · have : ret r = vis i w := by grind
      grind
  | tau t' => rw [tau_bind]; grind
  | vis i' k' =>
    rw [vis_bind]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨rfl, rfl⟩ : i = i' ∧ k ≍ fun o => k' o >>= f  := by grind
      grind
    · rintro (⟨_, h, _⟩ | ⟨k'', h, hk⟩)
      · grind
      · obtain ⟨rfl, rfl⟩ : i = i' ∧ k'' ≍ k' := by grind
        grind

end Bind

end ITree

namespace Subeffect


/-! ### `Subeffect.map` normalization -/

/-- The `E₁ -< (E₂ ⊕ₑ E')` instance from `E₁ -< E₂` maps to `Sum.inl`. -/
@[simp, grind =] theorem map_fst_eq_inl {E₁ E₂ E' : Effect} [E' -< E₁] (e : E'.I) :
    (map (E₂ := E₁ ⊕ₑ E₂) e).fst = Sum.inl (map e).fst := rfl

@[simp, grind =] theorem map_fst_eq_inr {E₁ E₂ E' : Effect} [E' -< E₂] (e : E'.I) :
    (map (E₂ := E₁ ⊕ₑ E₂) e).fst = Sum.inr (map e).fst := rfl
