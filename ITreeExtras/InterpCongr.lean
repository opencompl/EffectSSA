module

public import ITreeExtras.Definition
public import ITreeExtras.Basic
public import ITreeExtras.Bisim
public import ITreeExtras.HasEffect
public import ITreeExtras.Interp
public import ITreeExtras.Lift

/-!
# Congruence of `ITree.interp`

`interp_congr` states that `interp f t = interp g t` whenever the two
handlers `f` and `g` agree on every effect reachable from `t`.
-/

@[expose] public section
namespace ITree.ITree

variable {ε} {κε} [Effect.{u} ε κε]
         {δ} {κδ} [Effect.{u} δ κδ]
         {α}

theorem interp_congr {f g : ε ⤳ ITree δ} {t : ITree ε α}
    (hR₂ : ∀ e, t.HasEffect e → f e = g e) :
    interp f t = interp g t := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun x y =>
    ∃ α, ∃ t' : ITree δ α, ∃ k : α → ITree _ _,
        x = t' >>= (interp f <| k ·)
      ∧ y = t' >>= (interp g <| k ·)
      ∧ ∀ e o, (k o).HasEffect e → t.HasEffect e
  )
  · intro x y ⟨α, t', k, h⟩
    rcases h with ⟨hx, hy, h⟩
    subst hx hy
    cases t'
    case tau u =>
      right; left -- tau
      simp only [tau_bind]
      refine ⟨u >>= (interp f <| k ·), u >>= (interp g <| k ·), ?_⟩
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
          interp f (k x),
        fun o => do
          let x ← k' o
          interp g (k x),
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
        simp only [interp_vis, hfg]
        cases hg : g i
        case ret r =>
          right; left --tau
          refine ⟨interp f (k r), interp g (k r), ?_⟩
          and_intros
          · refine ⟨_, .ret r, k, ?_⟩
            grind
          · simp
          · simp
        case tau u =>
          right; left --tau
          simp only [tau_bind]
          refine ⟨u >>= fun o => tau (interp f <| k o),
                  u >>= fun o => tau (interp g <| k o),
                  ?_, rfl, rfl⟩
          refine ⟨_, u >>= (tau <| ret ·), k, ?_⟩;
          simp only [bind_assoc, tau_bind, bind_ret, true_and]
          grind
        case vis i' k' =>
          right; right --vis
          simp only [vis_bind]
          refine ⟨i',
            fun o => do
              let o ← k' o
              (interp f (k o)).tau,
            fun o => do
              let o ← k' o
              (interp g (k o)).tau, ?_⟩
          and_intros
          · intro o
            refine ⟨_, k' o >>= (tau <| ret ·), k, ?_⟩
            simp only [bind_assoc, tau_bind, bind_ret, true_and]
            grind
          · rfl
          · rfl
      case tau t =>
        right; left --tau
        simp only [interp_tau]
        refine ⟨interp f t, interp g t, ?_, rfl, rfl⟩
        refine ⟨PUnit, .ret ⟨⟩, fun _ => t, ?_⟩
        grind
      case ret r => simp
  · refine ⟨PUnit, .ret ⟨⟩, fun _ => t, ?_⟩
    simp

/-- Corrolary of `interp_congr`, specialized to `interpLeft`. -/
theorem interpLeft_congr {f g : ε ⤳ ITree δ} {t : ITree (ε ⊕ δ) α}
    (h : ∀ e : ε, t.HasEffect e → f e = g e) :
    t.interpLeft f = t.interpLeft g := by
  apply interp_congr
  intro e he
  cases e
  case inl e =>
    suffices f e = g e by simpa
    exact h _ he
  case inr e =>
    show Effect.trigger δ e = Effect.trigger δ e
    rfl
