module

public import ITree
public import ITreeExtras.Basic
public import ITreeExtras.Bisim
public import ITreeExtras.HasEffect
public import ITreeExtras.Interp

/-!
# Congruence of `ITree.interp`

`interp'_congr` states that `interp' f t = interp' g t` whenever the two
handlers `f` and `g` agree on every effect reachable from `t`.
-/

@[expose] public section
namespace ITree.ITree

theorem interp'_congr {f g : ε ⤳ ITree δ} {t : ITree ε α}
    (hR₂ : ∀ e, t.HasEffect e → f e = g e) :
    interp' f t = interp' g t := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun x y =>
    ∃ α, ∃ t' : ITree δ α, ∃ k : α → ITree _ _,
        x = t' >>= (interp' f <| k ·)
      ∧ y = t' >>= (interp' g <| k ·)
      ∧ ∀ e o, (k o).HasEffect e → t.HasEffect e
  )
  · intro x y ⟨α, t', k, h⟩
    rcases h with ⟨hx, hy, h⟩
    subst hx hy
    cases t'
    case tau u =>
      right; left -- tau
      simp only [tau_bind]
      refine ⟨u >>= (interp' f <| k ·), u >>= (interp' g <| k ·), ?_⟩
      and_intros
      · grind
      · rfl
      · rfl
    case vis i k' =>
      right; right -- vis
      simp only [vis_bind]
      refine ⟨i,
        fun o => do
          let x ← k' o
          interp' f (k x),
        fun o => do
          let x ← k' o
          interp' g (k x),
        ?_⟩
      and_intros
      · grind
      · rfl
      · rfl
    case ret a =>
      simp
      cases hk : k a
      case vis i k =>
        have : t.HasEffect i := by grind
        have hfg : f i = g i := by grind
        simp only [interp'_vis, hfg]
        cases hg : g i
        case ret r =>
          right; left --tau
          refine ⟨interp' f (k r), interp' g (k r), ?_⟩
          and_intros
          · refine ⟨_, .ret r, k, ?_⟩
            grind
          · simp
          · simp
        case tau u =>
          right; left --tau
          simp only [tau_bind]
          refine ⟨u >>= fun o => tau (interp' f <| k o),
                  u >>= fun o => tau (interp' g <| k o),
                  ?_, rfl, rfl⟩
          refine ⟨_, u >>= (tau <| ret ·), k, ?_⟩;
          grind
        case vis i' k' =>
          right; right --vis
          simp only [vis_bind]
          refine ⟨i',
            fun o => do
              let o ← k' o
              (interp' f (k o)).tau,
            fun o => do
              let o ← k' o
              (interp' g (k o)).tau, ?_⟩
          and_intros
          · intro o
            refine ⟨_, k' o >>= (tau <| ret ·), k, ?_⟩
            grind
          · rfl
          · rfl
      case tau t =>
        right; left --tau
        simp only [interp'_tau]
        refine ⟨interp' f t, interp' g t, ?_, rfl, rfl⟩
        refine ⟨PUnit, .ret ⟨⟩, fun _ => t, ?_⟩
        grind
      case ret r => simp; grind
  · refine ⟨PUnit, .ret ⟨⟩, fun _ => t, ?_⟩
    simp
