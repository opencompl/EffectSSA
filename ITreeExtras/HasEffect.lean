module

public import ITreeExtras.Definition

/-!
# ITree `HasEffect` and `MayReturn` Predicates
-/

@[expose] public section
namespace ITree.ITree
variable {ε} {κ} [Effect.{u} ε κ] {α : Type _}

/--
`t.HasEffect e` holds when the effect `e : ε` is used to label a node in tree
`t`, which is reachable in finitely many steps.
-/
inductive HasEffect : ITree ε α → ε → Prop where
  | vis_self {t i} {k : κ i → ITree ε α} :
      t.unfold = .vis i k → HasEffect t i
  | vis_cont {t i i'} {k : κ i' → ITree ε α} {o} :
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
  | vis {r i} {k : κ i → ITree ε α} {o : κ i} :
      t.unfold = .vis i k → MayReturn (k o) r → MayReturn t r


/-! ## Lemmas -/
section Lemmas
attribute [grind =] unfold_ret unfold_vis unfold_tau

/-! ### HasEffect -/

/-- `HasEffect` is transparent under `tau`. -/
@[simp, grind =] theorem hasEffect_tau {t : ITree ε α} {i : ε} :
    HasEffect (ITree.tau t) i ↔ HasEffect t i := by
  constructor
  · intro h; cases h <;> simp_all
  · exact HasEffect.tau (unfold_tau _)

/-- `ret _` carries no effects. -/
@[simp, grind .] theorem not_hasEffect_ret {r : α} {i : ε} :
    ¬HasEffect (ITree.ret (ε:=ε) r) i := by
  intro h; cases h <;> simp_all

@[simp, grind =] theorem hasEffect_vis {i j : ε} {k : κ i → ITree ε α} :
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

/-! ### MayReturn -/
section MayReturnLemmas

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

@[simp, grind =] theorem mayReturn_vis {i : ε} {k : κ i → ITree ε α} {x : α} :
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


/-! #### `bind` -/

/-- If `t` may return `x` and `f x` may return `y`, then `t >>= f` may return `y`. -/
theorem mayReturn_bind_of_mayReturn {t : ITree ε α} {f : α → ITree ε β}
    {x : α} {y : β} (hx : t.MayReturn x) (hy : (f x).MayReturn y) :
    (t >>= f).MayReturn y := by
  induction hx <;> grind

/--
`t >>= f` may return `y` iff `t` returns some `x` and `f x` returns `y`.
-/
@[simp, grind =] theorem mayReturn_bind {t : ITree ε α} {f : α → ITree ε β} {y : β} :
    (t >>= f).MayReturn y ↔ ∃ x, t.MayReturn x ∧ (f x).MayReturn y := by
  constructor
  · generalize hx : t >>= f = x
    intro h
    induction h generalizing t <;> grind
  · rintro ⟨x, hx, hy⟩
    exact mayReturn_bind_of_mayReturn hx hy

end MayReturnLemmas

/-! ### HasEffect of `bind` -/

/-- If `t` has effect `i`, so does `t >>= f` (regardless of `f`). -/
theorem hasEffect_bind_of_hasEffect_left {t : ITree ε α} (f : α → ITree ε β)
    (h : t.HasEffect i) : (t >>= f).HasEffect i := by
  induction h <;> grind

/-- If `t` may return `y` and `f y` has effect `i`, then so does `t >>= f`. -/
theorem hasEffect_bind_of_hasEffect_right {t : ITree ε α} {f : α → ITree ε β} {y : α}
    {i : ε} (hy : t.MayReturn y) (hf : (f y).HasEffect i) :
    (t >>= f).HasEffect i := by
  induction hy <;> grind

/--
`t >>= f` has effect `i` iff either `t` does or `t` may return a value `x` such that `f x` does.
-/
@[simp, grind =] theorem hasEffect_bind {t : ITree ε α} {f : α → ITree ε β} {i : ε} :
    (t >>= f).HasEffect i ↔ t.HasEffect i ∨ ∃ x, t.MayReturn x ∧ (f x).HasEffect i := by
  constructor
  · generalize hx : t >>= f = x
    intro h
    induction h generalizing t <;> grind
  · rintro (h | ⟨y, hy, hf⟩)
    · exact hasEffect_bind_of_hasEffect_left f h
    · exact hasEffect_bind_of_hasEffect_right hy hf

/-! ### HasEffect of `iter'` -/

@[grind →]
theorem hasEffect_iter' {α β : Type u} {f : α → ITree ε (α ⊕ β)} {a : α} :
    (iter' f a).HasEffect e → ∃ b, (f b).HasEffect e := by
  suffices
    ∀ (x : ITree ε β) (t' : ITree ε (α ⊕ β)),
      x = (t' >>= iter'.recurse f) →
      x.HasEffect e →
        t'.HasEffect e
        ∨ ∃ b, (f b).HasEffect e
  by
    specialize this (iter' f a) (f a) <| by rw [iter']
    grind
  intro x t' hx h
  induction h generalizing t'
  case vis_self i k hu =>
    subst hx
    cases t' with
    | vis => grind
    | tau => grind
    | ret r => cases r <;> simp_all
  case tau t i t'' ht hi  ih =>
    replace ht : t = tau t'' := by grind
    subst ht
    cases t' with
    | vis => grind
    | tau => grind
    | ret r =>
      cases r with
      | inr => simp_all
      | inl a' =>
        replace hx : t'' = iter' f a' := by simp_all
        subst hx
        specialize ih (f a') <| by rw [iter']
        cases ih <;> grind
  case vis_cont t i i' k e ht hk ih =>
    replace ht : t = vis i' k := by grind
    subst ht
    cases t'
    case tau => grind
    case vis i'' k' => grind
    case ret r =>
      cases r with
      | inl => grind
      | inr => simp only [pure_eq_ret, bind_ret, iter'.recurse_inr] at hx; grind

end Lemmas
end ITree.ITree
