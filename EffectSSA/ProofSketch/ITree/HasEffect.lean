module

public import ITreeExtras
public import ITreeExtras.Basic
public import ITreeExtras.HasEffect

/-!
# ITree `HasEffect` and `MayReturn` Predicates

`HasEffect` and `MayReturn` are now provided as inductive predicates by
`ITreeExtras.HasEffect`. This file provides additional lemmas.
-/

@[expose] public section
namespace ITree.ITree
variable {ε : Type} {κ : ε → Type} [Effect ε κ] {α : Type _}

/-! ## Lemmas -/
section Lemmas
attribute [grind =] unfold_ret unfold_vis unfold_tau

/-! ### HasEffect -/

@[simp, grind =]
theorem hasEffect_bind (t : ITree ε α) (f : α → ITree ε β) :
    (t >>= f).HasEffect e ↔ t.HasEffect e ∨ (∃ a, t.MayReturn a ∧ (f a).HasEffect e) := by
  sorry

@[simp, grind .]
axiom unfold_eq_vis_iff (t : ITree ε α) (i : ε) (k : κ i → ITree ε α) :
    t.unfold = .vis i k ↔ t = .vis i k


@[simp, grind .] theorem tau_neq_ret {t : ITree ε α} {x : α} : tau t ≠ ret x := by
  intro h; have := congrArg unfold h; simp at this

@[simp, grind .] theorem tau_neq_vis {t : ITree ε α} {i : ε}
    {k : κ i → ITree ε α} : tau t ≠ vis i k := by
  intro h; have := congrArg unfold h; simp at this

@[simp, grind .] theorem ret_neq_vis {x : α} {i : ε}
    {k : κ i → ITree ε α} : ret x ≠ vis i k := by
  intro h; have := congrArg unfold h; simp at this

/-- `vis` constructor injection (HEq form). -/
theorem vis_inj {i₁ i₂ : ε}
    {k₁ : κ i₁ → ITree ε α} {k₂ : κ i₂ → ITree ε α}
    (h : vis i₁ k₁ = vis i₂ k₂) : i₁ = i₂ ∧ HEq k₁ k₂ := by
  have hu := congrArg unfold h
  simpa only [unfold_vis, ITreeF.vis.injEq] using hu

@[simp, grind .] theorem ret_inj {x y : α} (h : @ret ε α x = ret y) : x = y := by
  have hu := congrArg unfold h
  simpa only [unfold_ret, ITreeF.ret.injEq] using hu

@[grind =]
theorem bind_eq_vis_iff (t : ITree ε α) (f : α → ITree ε β) (i : ε) (k : κ i → ITree ε β) :
    t >>= f = vis i k ↔
      (∃ x, t = ret x ∧ f x = vis i k)
      ∨ (∃ k', t = vis i k' ∧ k = fun o => k' o >>= f) := by
  cases t with
  | ret r =>
    rw [pure_bind]
    refine ⟨fun h => .inl ⟨r, rfl, h⟩, ?_⟩
    rintro (⟨w, hw, hf⟩ | ⟨w, h, _⟩)
    · obtain rfl : r = w := by simp_all; grind
      exact hf
    · have : ret r = vis i w := by grind
      grind
  | tau t' => rw [tau_bind]; grind
  | vis i' k' =>
    rw [vis_bind]
    refine ⟨fun h => ?_, ?_⟩
    · obtain ⟨rfl, hk⟩ := vis_inj h
      exact .inr ⟨k', rfl, (eq_of_heq hk).symm⟩
    · rintro (⟨_, h, _⟩ | ⟨k'', h, hk⟩)
      · grind
      · obtain ⟨rfl, hk'⟩ := vis_inj h
        rw [hk, eq_of_heq hk']

section Iter

@[grind →]
axiom hasEffect_iter {β} {f : α → ITree ε (α ⊕ β)} {a : α} {e : ε} :
    (ITree.iter f a).HasEffect e → ∃ b, (f b).HasEffect e

end Iter

/-! ### MayReturn -/


end Lemmas
end ITree.ITree
