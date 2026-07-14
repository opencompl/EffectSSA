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

/--
Translate an ITree along a subeffect inclusion `[ε -< δ]`.
-/
def lift [ε -< δ] : ITree ε α → ITree δ α :=
  interp fun i =>
    let ⟨j, k⟩ := Subeffect.map i
    .vis j (.ret ∘ k)

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
  simp [lift]

@[simp, grind =] theorem lift_vis (i : ε) (k : κε i → ITree ε α) :
    lift (δ := δ) (vis i k)
      = vis (Subeffect.map i).1
          (fun x => tau (lift (k ((Subeffect.map i).2 x)))) := by
  simp only [lift, interp_vis, vis_bind, bind_ret, Function.comp]

@[simp]
theorem liftM_eq_lift (t : ITree ε α) :
    liftM (n:=ITree δ) t = lift (δ := δ) t := rfl

@[simp, grind =] theorem lift_eq_ret_iff (t : ITree ε α) (r : α) :
    t.lift (δ:=δ) = ret r ↔ t = ret r := by
  simp [lift]

@[simp] theorem lift_eq_tau_iff (t : ITree ε α) :
    t.lift (δ:=δ) = tau t' ↔ ∃ u, t = tau u ∧ t' = u.lift := by
  cases t <;> (simp; grind)

open Subeffect (map) in
@[simp] theorem lift_eq_vis_iff (t : ITree ε α) :
    t.lift (δ:=δ) (κδ:=κδ) = vis i k ↔ ∃ j l,
      t = vis j l
      ∧ i = (map j).1
      ∧ k ≍ (fun x => tau <| (l ((map (ε₂:=δ) j).2 x)).lift (δ:=δ)) := by
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
          ∧ k ≍ fun x => (l ((map j).snd x)).lift.tau := by
        simpa using ht
      specialize ih (l ((map j).snd o)).tau
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

open Subeffect (map) in
@[simp, grind =]
theorem hasEffect_liftM (t : ITree ε α) {e : δ} :
    (liftM (n:=ITree δ) t).HasEffect e ↔
      ∃ e', t.HasEffect e' ∧ (Subeffect.map e').fst = e := by
  rw [liftM_eq_lift]
  constructor
  · suffices h : ∀ (t' : ITree δ α) (t : ITree ε α), t' = t.lift → t'.HasEffect e →
        ∃ e', t.HasEffect e' ∧ (Subeffect.map e').fst = e by
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
        obtain rfl : (Subeffect.map i₀).fst = i' := by grind
        specialize ih (tau (k₀ ((Subeffect.map i₀).2 o)))
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
end Lemmas

end ITree
end ITree
