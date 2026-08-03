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

variable {ε} {κ} [Effect.{u} ε κ] {α β}

namespace ITree
variable {t : ITree ε α}

coinductive BisimUpTo (R : α → β → Prop) : ITree ε α → ITree ε β → Prop where
  | ret : R x y → BisimUpTo R (.ret x) (.ret y)
  | tau : BisimUpTo R s₁ s₂ → BisimUpTo R (.tau s₁) (.tau s₂)
  | vis : (∀ o : κ i, BisimUpTo R (k₁ o) (k₂ o)) → BisimUpTo R (.vis i k₁) (.vis i k₂)

/--
Strong bisimilarity for ITrees.
Both trees must unfold to the same constructor, and continuations must again be bisimilar.
-/
coinductive Bisim : ITree ε α → ITree ε α → Prop where
  | ret : Bisim (.ret r) (.ret r)
  | tau : Bisim s₁ s₂ → Bisim (.tau s₁) (.tau s₂)
  | vis : (∀ o : κ i, Bisim (k₁ o) (k₂ o)) → Bisim (.vis i k₁) (.vis i k₂)

end ITree

-- Scope `≅` notation to top-level ITree namespace, rather than inner `ITree.ITree`
scoped infixl:arg " ≅ " => ITree.Bisim

namespace ITree

@[simp, grind =]
theorem bisimUpTo_eq {x y : ITree ε α} : BisimUpTo (· = ·) x y ↔ x ≅ y := by
  constructor <;> intro h
  · apply Bisim.coinduct (BisimUpTo (· = ·) · ·) _ _ _ h
    intro t u htu; cases htu <;> grind
  · apply BisimUpTo.coinduct _ (· ≅ ·) _ _ _ h
    intro t u htu; cases htu <;> grind

/-- Bisimilar ITrees are equal. -/
theorem eq_of_bisim {t₁ t₂ : ITree ε α} (h : t₁.Bisim t₂) : t₁ = t₂ := by
  ext n
  induction n generalizing t₁ t₂
  · rfl
  · cases h <;> grind

section Equiv

-- Reflexivity

@[simp, grind .]
theorem bisimUpTo_refl_of (hR : ∀ x, R x x) (x : ITree ε α) : BisimUpTo R x x := by
  apply BisimUpTo.coinduct R (· = ·)
  · rintro x _ rfl
    cases x
    case ret => simp [hR]
    case tau => simp
    case vis i k =>
      right; right
      refine ⟨i, k, k, ?_⟩
      simp
  · rfl

@[refl] theorem bisimUpTo_refl [Std.Refl R] (x : ITree ε α) : BisimUpTo R x x := by
  simp [Std.Refl.refl]

@[refl, simp, grind .]
theorem bisim_refl (x : ITree ε α) : x ≅ x := by
  suffices BisimUpTo (· = ·) x x by grind
  grind

/--
One-step observation of `BisimUpTo`: either both trees are `ret`s with related values,
or both are `tau`s with a bisimilar subtree, or both are `vis`s with bisimilar continuations.
-/
theorem BisimUpTo.destruct {a : ITree ε α} {b : ITree ε β} (h : BisimUpTo R a b) :
    (∃ x y, R x y ∧ a = .ret x ∧ b = .ret y)
    ∨ (∃ s₁ s₂, BisimUpTo R s₁ s₂ ∧ a = .tau s₁ ∧ b = .tau s₂)
    ∨ (∃ i k₁ k₂,
        (∀ o : κ i, BisimUpTo R (k₁ o) (k₂ o)) ∧ a = .vis i k₁ ∧ b = .vis i k₂) := by
  rw [BisimUpTo.functor_unfold] at h
  exact (BisimUpTo._functor.existential_equiv ..).mp h

-- Transitivity

@[grind →]
theorem bisimUpTo_trans_of (hR : ∀ x y z, R x y → R y z → R x z)
    {t₁ t₂ t₃ : ITree ε α} (h₁ : BisimUpTo R t₁ t₂) (h₂ : BisimUpTo R t₂ t₃) :
    BisimUpTo R t₁ t₃ := by
  apply BisimUpTo.coinduct R (fun a c => ∃ b, BisimUpTo R a b ∧ BisimUpTo R b c)
  · rintro a c ⟨b, hab, hbc⟩
    rcases hab.destruct with ⟨x, y, hxy, rfl, rfl⟩
                          | ⟨s₁, s₂, hs, rfl, rfl⟩
                          | ⟨i, k₁, k₂, hk, rfl, rfl⟩
    · rcases hbc.destruct with ⟨y', z, hyz, hb, rfl⟩ | ⟨_, _, _, hb, _⟩ | ⟨_, _, _, _, hb, _⟩
      · simp at hb; subst hb
        exact .inl ⟨_, _, hR _ _ _ hxy hyz, rfl, rfl⟩
      · exact absurd hb.symm tau_neq_ret
      · exact absurd hb ret_neq_vis
    · rcases hbc.destruct with ⟨_, _, _, hb, _⟩ | ⟨s₂', s₃, hs', hb, rfl⟩ | ⟨_, _, _, _, hb, _⟩
      · exact absurd hb tau_neq_ret
      · simp at hb; subst hb
        exact .inr <| .inl ⟨_, _, ⟨_, hs, hs'⟩, rfl, rfl⟩
      · exact absurd hb tau_neq_vis
    · rcases hbc.destruct with ⟨_, _, _, hb, _⟩ | ⟨_, _, _, hb, _⟩ | ⟨i', k₂', k₃, hk', hb, rfl⟩
      · exact absurd hb.symm ret_neq_vis
      · exact absurd hb.symm tau_neq_vis
      · simp at hb; obtain ⟨rfl, hb⟩ := hb; cases hb
        exact .inr <| .inr ⟨_, _, _, fun o => ⟨_, hk o, hk' o⟩, rfl, rfl⟩
  · exact ⟨t₂, h₁, h₂⟩

theorem bisimUpTo_trans [Trans R R R] {t₁ t₂ t₃ : ITree ε α}
    (h₁ : BisimUpTo R t₁ t₂) (h₂ : BisimUpTo R t₂ t₃) : BisimUpTo R t₁ t₃ :=
  bisimUpTo_trans_of (fun x _ z (hxy : R x _) hyz => (Trans.trans hxy hyz : R x z)) h₁ h₂

@[grind →]
theorem bisim_trans {t₁ t₂ t₃ : ITree ε α} (h₁ : t₁ ≅ t₂) (h₂ : t₂ ≅ t₃) : t₁ ≅ t₃ :=
  eq_of_bisim h₁ ▸ h₂

-- Antisymmetry

@[grind .]
theorem bisimUpTo_antisymm_of (hR : ∀ x y, R x y → R y x → x = y)
    {t₁ t₂ : ITree ε α} (h₁ : BisimUpTo R t₁ t₂) (h₂ : BisimUpTo R t₂ t₁) : t₁ = t₂ := by
  suffices BisimUpTo (· = ·) t₁ t₂ by grind [eq_of_bisim]
  apply BisimUpTo.coinduct (· = ·) (fun a b => BisimUpTo R a b ∧ BisimUpTo R b a)
  · rintro a b ⟨hab, hba⟩
    rcases hab.destruct with ⟨x, y, hxy, rfl, rfl⟩
                          | ⟨s₁, s₂, hs, rfl, rfl⟩
                          | ⟨i, k₁, k₂, hk, rfl, rfl⟩
    · rcases hba.destruct with ⟨y', x', hyx, hb, ha⟩ | ⟨_, _, _, hb, _⟩ | ⟨_, _, _, _, hb, _⟩
      · simp at hb ha; subst hb; subst ha
        exact .inl ⟨_, _, hR _ _ hxy hyx, rfl, rfl⟩
      · exact absurd hb.symm tau_neq_ret
      · exact absurd hb ret_neq_vis
    · rcases hba.destruct with ⟨_, _, _, hb, _⟩ | ⟨s₂', s₁', hs', hb, ha⟩ | ⟨_, _, _, _, hb, _⟩
      · exact absurd hb tau_neq_ret
      · simp at hb ha; subst hb; subst ha
        exact .inr <| .inl ⟨_, _, ⟨hs, hs'⟩, rfl, rfl⟩
      · exact absurd hb tau_neq_vis
    · rcases hba.destruct with ⟨_, _, _, hb, _⟩ | ⟨_, _, _, hb, _⟩ | ⟨i', k₂', k₁', hk', hb, ha⟩
      · exact absurd hb.symm ret_neq_vis
      · exact absurd hb.symm tau_neq_vis
      · simp at hb ha
        obtain ⟨rfl, hb⟩ := hb; cases hb
        obtain ⟨_, ha⟩ := ha; cases ha
        exact .inr <| .inr ⟨_, _, _, fun o => ⟨hk o, hk' o⟩, rfl, rfl⟩
  · exact ⟨h₁, h₂⟩

theorem bisimUpTo_antisymm [Std.Antisymm R] {t₁ t₂ : ITree ε α}
    (h₁ : BisimUpTo R t₁ t₂) (h₂ : BisimUpTo R t₂ t₁) : t₁ = t₂ :=
  bisimUpTo_antisymm_of Std.Antisymm.antisymm h₁ h₂

@[grind .]
theorem bisim_antisymm {t₁ t₂ : ITree ε α} (h₁ : t₁ ≅ t₂) (_ : t₂ ≅ t₁) : t₁ = t₂ :=
  eq_of_bisim h₁

