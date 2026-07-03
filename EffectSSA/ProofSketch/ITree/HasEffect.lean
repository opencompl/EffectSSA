module

public import ITree

/-!
# ITree `HasEffect` and `MayReturn` Predicates
-/

@[expose] public section
namespace ITree.ITree
variable {ε : Effect} {α : Type _}

/--
`t.HasEffect e` holds when the effect `e : ε.I` is used to label a node in tree
`t` that is reachable in finitely many steps.
-/
inductive HasEffect : ITree ε α → ε.I → Prop where
  | vis_self {t i} {k : ε.O i → ITree ε α} :
      t.unfold = .vis i k → HasEffect t i
  | vis_cont {t i i'} {k : ε.O i' → ITree ε α} {o} :
      t.unfold = .vis i' k → HasEffect (k o) i → HasEffect t i
  | tau {t i t'} :
      t.unfold = .tau t' → HasEffect t' i → HasEffect t i

/--
`t.MayReturn x` holds when there is a leaf `ret x` in tree `t`,
which is reachable in finitely many steps.
-/
inductive MayReturn : ITree ε α → α → Prop where
  | ret : t.unfold = .ret r → MayReturn t r
  | tau {t r t'} : t.unfold = .tau t' → MayReturn t' r → MayReturn t r
  | vis {r i} {k : ε.O i → ITree ε α} {o : ε.O i} :
      t.unfold = .vis i k → MayReturn (k o) r → MayReturn t r


/-! ## Lemmas -/
section Lemmas
attribute [grind =] unfold_ret unfold_vis unfold_tau

/-! ### HasEffect -/

section Basic

/-- `HasEffect` is transparent under `tau`. -/
@[simp, grind =] theorem hasEffect_tau {t : ITree ε α} {i : ε.I} :
    HasEffect (ITree.tau t) i ↔ HasEffect t i := by
  constructor
  · intro h; cases h <;> simp_all
  · exact HasEffect.tau (unfold_tau _)

/-- `ret _` carries no effects. -/
@[simp, grind .] theorem not_hasEffect_ret {r : α} {i : ε.I} :
    ¬HasEffect (ITree.ret r) i := by
  intro h; cases h <;> simp_all

@[simp, grind ·] theorem not_hasEffect_pure {r : α} {i : ε.I} :
    ¬HasEffect (pure r) i :=
  not_hasEffect_ret

@[simp, grind =] theorem hasEffect_vis {i j : ε.I} {k : ε.O i → ITree ε α} :
    (ITree.vis i k).HasEffect j ↔ i = j ∨ (∃ o, (k o).HasEffect j) := by
  constructor
  · intro h
    cases h using HasEffect.casesOn with
    | tau => simp_all
    | vis_self => simp_all
    | @vis_cont _ _ i₂ k' i₃ h₁ h₂ =>
      obtain rfl : i = i₂ := by grind
      simp_all only [unfold_vis, ITreeF.vis.injEq, heq_eq_eq, true_and]
      grind
  · rintro (rfl|h)
    · exact HasEffect.vis_self rfl
    · exact .vis_cont rfl h.choose_spec

@[simp, grind =]
theorem hasEffect_bind (t : ITree ε α) (f : α → ITree ε β) :
    (t >>= f).HasEffect e ↔ t.HasEffect e ∨ (∃ a, t.MayReturn a ∧ (f a).HasEffect e) := by
  sorry

@[simp, grind .]
axiom unfold_eq_vis_iff (t : ITree ε α) (i) (k) :
    t.unfold = .vis i k ↔ t = .vis i k

@[simp, grind .] theorem tau_neq_ret {t : ITree ε α} {x : α} : tau t ≠ ret x := by
  intro h; have := congrArg unfold h; simp at this

@[simp, grind .] theorem tau_neq_vis {t : ITree ε α} {i : ε.I}
    {k : ε.O i → ITree ε α} : tau t ≠ vis i k := by
  intro h; have := congrArg unfold h; simp at this

@[simp, grind .] theorem ret_neq_vis {x : α} {i : ε.I}
    {k : ε.O i → ITree ε α} : ret x ≠ vis i k := by
  intro h; have := congrArg unfold h; simp at this

@[simp, grind =_]
theorem pure_eq_ret : (pure x : ITree ε α) = ret x := by rfl

-- grind_pattern pure_eq_ret => (pure x : ITree ε α)

@[simp, grind .] theorem vis_inj {i₁ i₂ : ε.I}
    {k₁ : ε.O i₁ → ITree ε α} {k₂ : ε.O i₂ → ITree ε α}
    (h : vis i₁ k₁ = vis i₂ k₂) :
    i₁ = i₂ ∧ k₁ ≍ k₂ := by
  have hu := congrArg unfold h
  simpa only [unfold_vis, ITreeF.vis.injEq] using hu

@[simp, grind .] theorem ret_inj {x y : α} (h : @ret ε α x = ret y) : x = y := by
  have hu := congrArg unfold h
  simpa only [unfold_ret, ITreeF.ret.injEq] using hu

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

end Basic

section Iter

def iter' {α β} (t : α → ITree E (α ⊕ β)) : α → ITree E β := fun a => do
  match ← (t a) with
  | .inl a => tau <| .iter' t a
  | .inr b => return b
partial_fixpoint

-- inductive HasEffectIter (e : ε.I) (f : α → ITree ε (α ⊕ β)) : α → Prop
--   | self : (f a).HasEffect e → HasEffectIter e f a
--   | step :
--       f a = .inl a → HasEffectIter e f a'
--       → HasEffectIter e f a

@[grind →]
axiom hasEffect_iter : (iter f a).HasEffect e → ∃ b, (f b).HasEffect e -- := by
  -- generalize hx : iter' f a = x
  -- intro h
  -- induction h
  -- case vis_self i k hu =>
  --   subst hx
  --   rw (occs:=[1]) [ITree.iter'] at hu
  --   simp only [unfold_eq_vis_iff, pure_eq_ret, bind_eq_vis_iff] at hu
  --   rcases hu with (⟨a'|b, hu⟩|hu)
  --   <;> grind
  -- case tau t i t' ht' hi  ih =>
  --   obtain rfl : t = tau t' := by sorry
  --   rw (occs:=[1]) [ITree.iter'] at hx
  --   -- have : ∃ a', (f a) = .inl a' ∧ ()
  --   sorry
  -- case vis_cont =>
  --   sorry


end Iter

/-! ### MayReturn -/

/-- `ret x` returns only `x`. -/
@[simp, grind =] theorem mayReturn_ret {r x : α} :
    MayReturn (ε := ε) (ITree.ret r) x ↔ x = r := by
  constructor
  · intro h; cases h <;> simp_all
  · rintro rfl
    exact MayReturn.ret (unfold_ret _)

/-- `MayReturn` is transparent under `tau`. -/
@[simp, grind =] theorem mayReturn_tau {t : ITree ε α} {x : α} :
    MayReturn (ITree.tau t) x ↔ MayReturn t x := by
  constructor
  · intro h; cases h <;> simp_all
  · exact MayReturn.tau (unfold_tau t)

@[simp, grind =] theorem mayReturn_vis {i : ε.I} {k : ε.O i → ITree ε α} {x : α} :
    MayReturn (ITree.vis i k) x ↔ ∃ o, MayReturn (k o) x := by
  constructor
  · intro h
    cases h with
    | ret _ | tau _ _ => simp_all
    | @vis _ _ i₁ k₁ o₁ h hh =>
        obtain rfl : i = i₁ := by grind
        obtain rfl : k = k₁ := by grind
        exact ⟨o₁, hh⟩
  · rintro ⟨o, ho⟩
    exact MayReturn.vis (unfold_vis i k) ho

end Lemmas
end ITree.ITree
