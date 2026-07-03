module

public import ITree
public import EffectSSA.ProofSketch.ITree.InterpM
public import EffectSSA.ProofSketch.ITree.HasEffect

/-!
# ITree Axioms
-/
@[expose] public section
namespace ITree.ITree

-- Monad Lifting via Subeffects

def lift [ε -< δ] : ITree ε α → ITree δ α :=
  interpM fun i =>
    let ⟨j, k⟩ := Subeffect.map i
    .vis j (.ret ∘ k)

/-- NOTE: the following instance cannot be defined on `MonadLift`, given that
class's first argument is an `outParam`, so we define `MonadLiftT` directly. -/
instance [ε -< δ] : MonadLiftT (ITree ε) (ITree δ) where
  monadLift := lift

def forever : ITree ε α :=
  .tau <| forever
partial_fixpoint

@[simp]
axiom lift_forever [ε -< δ] : @lift ε δ α _ .forever = .forever
attribute [grind .] lift_forever

axiom interp_vis_with_tau {F} (f : (i : E.I) → ITree F (E.O i)) i (k : E.O i → ITree E R) :
  ITree.interp f (ITree.vis i k) = do
    let o ← f i
    (ITree.interp f (k o)).tau

@[simp, grind =] theorem bind_ret : ret r >>= f = f r := by
  show pure r >>= f = _
  simp [-pure_eq_ret]

attribute [grind =] tau_bind LawfulMonad.bind_assoc interp_pure interp_ret interp_tau
attribute [-simp] interp_vis
attribute [simp, grind .] interp_vis_with_tau

@[simp, grind .]
theorem pure_eq : pure x = ret (E:=E) x := by rfl

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

      simp [- pure_eq_ret, -vis_inj]

      stop
      cases hk : k a
      case vis i k =>
        have : t.HasEffect i := by grind
        have hfg : f i = g i := by grind
        simp only [interp_vis_with_tau, hfg]
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
            grind
          · rfl
          · rfl
      case tau t =>
        right; left --tau
        simp only [interp_tau]
        refine ⟨interp f t, interp g t, ?_, rfl, rfl⟩
        refine ⟨PUnit, .ret ⟨⟩, fun _ => t, ?_⟩
        grind
      case ret r => simp; grind
  · refine ⟨PUnit, .ret ⟨⟩, fun _ => t, ?_⟩
    simp
