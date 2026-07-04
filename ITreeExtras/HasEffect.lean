module

public import ITree

/-!
# ITree `HasEffect` and `MayReturn` Predicates
-/

@[expose] public section
namespace ITree.ITree
variable {ε : Effect} {α : Type _}

/--
`t.HasEffect e` holds when the effect `e : ε.I` is used to label any node in tree `t`.
-/
coinductive HasEffect : ITree ε α → ε.I → Prop where
  | vis_self {t i} {k : ε.O i → ITree ε α} :
      t.unfold = .vis i k → HasEffect t i
  | vis_cont {t i i'} {k : ε.O i' → ITree ε α} {o} :
      t.unfold = .vis i' k → HasEffect (k o) i → HasEffect t i
  | tau {t i t'} :
      t.unfold = .tau t' → HasEffect t' i → HasEffect t i

/--
`t.MayReturn x` holds when there is a leaf `ret x` anywhere in tree `t`.
-/
coinductive MayReturn : ITree ε α → α → Prop where
  | ret : t.unfold = .ret r → MayReturn t r
  | tau {t r t'} : t.unfold = .tau t' → MayReturn t' r → MayReturn t r
  | vis {r i} {k : ε.O i → ITree ε α} {o : ε.O i} :
      t.unfold = .vis i k → MayReturn (k o) r → MayReturn t r


/-! ## Lemmas -/
section Lemmas
attribute [grind =] unfold_ret unfold_vis unfold_tau

/-! ### HasEffect -/

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
