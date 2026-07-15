module

public import ITreeExtras.Definition
public import ITreeExtras.InterpM
public import ITreeExtras.Basic
public import ITreeExtras.Interp
public import ITreeExtras.HasEffect

/-!
# Lifting ITrees along subeffects

Given an inclusion of effects `[ε -< δ]`, we can lift a computation from
`ITree ε α` into `ITree δ α` by translating each visible effect.
-/

@[expose] public section
namespace ITree
variable {ε} {κε} [Effect.{u} ε κε] {δ} {κδ} [Effect.{u} δ κδ] {α}

namespace Effect

instance instCoeTOfSubeffect [ε -< δ] {e} : CoeT ε e δ where
  coe := (Subeffect.map e).1

end Effect

namespace ITree
open Subeffect (map mapEff mapCont)

/--
Translate an ITree along a subeffect inclusion `[ε -< δ]`.
-/
def lift [ε -< δ] (t : ITree ε α) : ITree δ α :=
  match t.unfold with
  | .ret x => .ret x
  | .tau u => .tau u.lift
  | .vis i k => .vis (mapEff i) (fun o => k (mapCont i o) |>.lift)
  partial_fixpoint

/-- NOTE: the following instance cannot be defined on `MonadLift`, given that
class's first argument is an `outParam`, so we define `MonadLiftT` directly. -/
instance [ε -< δ] : MonadLiftT (ITree ε) (ITree δ) where
  monadLift := lift

/-!
## Lemmas
-/
section Lemmas
variable [ε -< δ]

/-! ### Basic -/
section Basic

@[simp, grind =] theorem lift_ret (r : α) :
    lift (ε := ε) (δ := δ) (ret r) = ret r := by
  simp [lift]

@[simp, grind =] theorem lift_tau (t : ITree ε α) :
    lift (δ := δ) (tau t) = tau (lift t) := by
  conv => {lhs; rw [lift]}
  simp

@[simp, grind =] theorem lift_vis (i : ε) (k : κε i → ITree ε α) :
    lift (δ := δ) (vis i k)
    = vis (mapEff i) (fun o => k (mapCont i o) |>.lift) := by
  conv => {lhs; rw [lift]}
  simp

@[simp, grind =] theorem lift_eq_ret_iff (t : ITree ε α) (r : α) :
    t.lift (δ:=δ) = ret r ↔ t = ret r := by
  rw [lift]; grind

@[simp] theorem lift_eq_tau_iff (t : ITree ε α) :
    t.lift (δ:=δ) = tau t' ↔ ∃ u, t = tau u ∧ t' = u.lift := by
  rw [lift]; grind

open Subeffect (map) in
@[simp] theorem lift_eq_vis_iff (t : ITree ε α) :
    t.lift (δ:=δ) (κδ:=κδ) = vis i k ↔ ∃ j l,
      t = vis j l
      ∧ i = (map j).1
      ∧ k ≍ (fun x => (l ((map (ε₂:=δ) j).2 x)).lift (δ:=δ)) := by
  cases t
  case ret => simp
  case tau => simp
  case vis j l =>
    simp only [lift_vis, vis_inj]
    constructor
    · grind
    · rintro ⟨j, l, ⟨rfl, rfl⟩, rfl, rfl⟩
      and_intros <;> rfl

end Basic

/-! ### Lifting Monadic Ops -/
section Monadic

@[simp, grind =_]
-- NOTE: for some reason, `grind =` is not accepted here, thus we choose to
--       *invert* the direction of the grind-lemma, w.r.t. the simp-lemma.
theorem liftM_eq_lift (t : ITree ε α) :
    liftM (n:=ITree δ) t = lift (δ := δ) t := rfl

@[simp, grind =] theorem lift_pure (r : α) :
    (lift (pure r : ITree ε _) : ITree δ _) = pure r := by simp

@[simp, grind =]
theorem lift_bind (t : ITree ε α) (k : α → ITree ε β) :
    (lift (t >>= k) : ITree δ _) = t.lift >>= (k · |>.lift) := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun (x y : ITree δ β) =>
    ∃ (α₀ : Type u) (u : ITree ε α₀) (k : α₀ → ITree ε β),
        x = lift (δ := δ) (u >>= k)
      ∧ y = u.lift >>= (fun a => (k a).lift))
  · rintro x y ⟨α₀, u, k, rfl, rfl⟩
    cases u with
    | tau u' =>
      simp only [tau_bind, lift_tau]
      right; left
      exact ⟨_, _, ⟨_, u', k, rfl, rfl⟩, rfl, rfl⟩
    | vis j k'' =>
      simp only [vis_bind, lift_vis]
      right; right
      refine ⟨mapEff j, _, _,
              fun o => ⟨_, k'' (mapCont j o), k, rfl, rfl⟩, rfl, rfl⟩
    | ret a =>
      simp only [pure_bind, lift_pure]
      cases k a with
      | ret r => simp
      | tau t' =>
        simp only [lift_tau]
        right; left
        refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => t', ?_⟩, rfl, rfl⟩
        simp
      | vis i k'' =>
        simp only [lift_vis]
        right; right
        refine ⟨mapEff i, _, _,
                fun o => ⟨_, ret ⟨⟩, fun _ : PUnit => k'' (mapCont i o), ?_⟩,
                rfl, rfl⟩
        simp
  · exact ⟨α, t, k, rfl, rfl⟩

instance : LawfulMonadLiftT (ITree ε) (ITree δ) where
  monadLift_pure := lift_pure
  monadLift_bind := lift_bind

@[simp]
theorem lift_seqRight (t : ITree ε α) (u : ITree ε β) :
    ((t *> u).lift : ITree δ _) = t.lift *> u.lift := by
  simp [← liftM_eq_lift]

end Monadic

/-! ### MayReturn -/
section MayReturn

open Subeffect (map) in
@[simp, grind =]
theorem mayReturn_liftM (t : ITree ε α) :
    (liftM (n:=ITree δ) t).MayReturn x ↔ t.MayReturn x := by
  rw [liftM_eq_lift]
  constructor
  · generalize ht : t.lift (δ:=δ) = t'
    intro h
    induction h generalizing t
    case ret r _ =>
      replace ht : t.lift (δ:=δ) = .ret r := by grind
      obtain rfl : t = .ret r := by simp_all
      grind
    case tau r t' _ hr ih =>
      replace ht : t.lift (δ:=δ) = .tau t' := by grind
      obtain ⟨u, rfl, rfl⟩ : ∃ u, t = tau u ∧ t' = u.lift := by simpa using ht
      grind
    case vis r i k o _ hr ih =>
      replace ht : t.lift (δ:=δ) = .vis i k := by grind
      obtain ⟨j, l, ⟨rfl, rfl⟩, rfl, rfl⟩ : ∃ j l,
          t = vis j l
          ∧ i = (map j).fst
          ∧ k ≍ fun x => (l ((map j).snd x)).lift := by
        simpa using ht
      specialize ih (l ((map j).snd o))
      grind
  · intro h
    induction h
    case ret => grind
    case tau => grind
    case vis t r i k o ht hk hkl =>
      replace ht : t = vis i k := by grind
      subst ht
      let mi := (map (ε₂:=δ) i).2
      obtain ⟨o, rfl⟩ : ∃ o', mi o' = o := by
        suffices mi.Surjective by apply this
        grind
      grind

end MayReturn

/-! ### HasEffect -/
section HasEffect

@[simp, grind =]
theorem hasEffect_liftM (t : ITree ε α) {e : δ} :
    (liftM (n:=ITree δ) t).HasEffect e ↔
      ∃ e', t.HasEffect e' ∧ mapEff e' = e := by
  rw [liftM_eq_lift]
  constructor
  · suffices h : ∀ (t' : ITree δ α) (t : ITree ε α), t' = t.lift → t'.HasEffect e →
        ∃ e', t.HasEffect e' ∧ mapEff e' = e by
      grind
    intro t' t ht h_eff
    induction h_eff generalizing t with
    | vis_self => cases t <;> simp_all
    | tau => cases t <;> simp_all
    | @vis_cont u i i' k o hu _ ih =>
      cases t with
      | ret r => simp_all
      | tau t' => simp_all
      | vis i₀ k₀ =>
        obtain rfl : mapEff i₀ = i' := by grind
        specialize ih (k₀ (mapCont i₀ o))
        grind
  · rintro ⟨e', he', rfl⟩
    induction he' with
    | vis_self => grind
    | tau => grind
    | @vis_cont t' j j' k o hu h ih =>
      let mi := (map (ε₂:=δ) j').2
      obtain ⟨o, rfl⟩ : ∃ o', mi o' = o := by
        suffices mi.Surjective by apply this
        grind
      grind

end HasEffect

/-! ### Interp -/
section Interp
variable {η κη} [Effect.{u} η κη]

open Subeffect (mapEff mapCont)

/-- Interpretation composes with `lift` -/
theorem interp_lift (f : δ ⤳ ITree η) (t : ITree ε α) :
    interp f (lift (δ := δ) t)
      = interp (fun i : ε => do
          let x ← (f (mapEff i))
          return mapCont _ x
          ) t := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun (x y : ITree η α) =>
    ∃ (α₀ : Type u) (u : ITree η α₀) (k : α₀ → ITree ε α),
        x = u >>= (fun a => interp f (lift (δ := δ) (k a)))
      ∧ y = u >>= (fun a => interp (fun i : ε => do
          let x ← (f (mapEff i))
          return mapCont i x) (k a)))
  · rintro x y ⟨α₀, u, k, rfl, rfl⟩
    cases u with
    | tau u' =>
      simp only [tau_bind]
      right; left
      exact ⟨_, _, ⟨_, u', k, rfl, rfl⟩, rfl, rfl⟩
    | vis j k'' =>
      simp only [vis_bind]
      right; right
      exact ⟨j, _, _, fun o => ⟨_, k'' o, k, rfl, rfl⟩, rfl, rfl⟩
    | ret a =>
      simp only [pure_bind]
      cases k a with
      | ret r => simp
      | tau t' =>
        simp only [lift_tau, interp_tau]
        right; left
        refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => t', ?_⟩, rfl, rfl⟩
        simp
      | vis i k'' =>
        simp only [lift_vis, interp_vis, bind_assoc, pure_bind]
        cases f (mapEff i) with
        | ret o =>
          simp only [pure_bind]
          right; left
          refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => k'' (mapCont i o), ?_⟩, rfl, rfl⟩
          simp
        | tau t' =>
          simp only [tau_bind]
          right; left
          refine ⟨_, _, ⟨_, t', fun x => tau (k'' (mapCont i x)), ?_⟩, rfl, rfl⟩
          simp
        | vis j k''' =>
          simp only [vis_bind]
          right; right
          refine ⟨j, _, _,
                  fun o' => ⟨_, k''' o', fun x => tau (k'' (mapCont i x)), ?_⟩,
                  rfl, rfl⟩
          simp
  · refine ⟨PUnit, ret ⟨⟩, fun _ => t, ?_⟩
    simp

end Interp

end Lemmas

end ITree
end ITree
