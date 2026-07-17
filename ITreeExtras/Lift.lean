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

The primitive operation is `ITree.map`, which translates an ITree along an
explicit pair of maps on effects and continuations. `ITree.lift` is then
defined as the specialization of `map` at the maps supplied by a
`Subeffect` instance.
-/

@[expose] public section
namespace ITree
variable {ε} {κε} [Effect.{u} ε κε] {δ} {κδ} [Effect.{u} δ κδ] {α}

namespace Effect

instance instCoeTOfSubeffect [ε -< δ] {e} : CoeT ε e δ where
  coe := (Subeffect.map e).1

end Effect

namespace ITree
open Subeffect (mapEff mapCont)

/--
Translate an ITree along explicit maps on effects and continuations.
-/
def map (fEff : ε → δ) (fCont : (i : ε) → κδ (fEff i) → κε i)
    (t : ITree ε α) : ITree δ α :=
  match t.unfold with
  | .ret x => .ret x
  | .tau u => .tau (u.map fEff fCont)
  | .vis i k => .vis (fEff i) (fun o => (k (fCont i o)).map fEff fCont)
  partial_fixpoint

/--
Translate an ITree along a subeffect inclusion `[ε -< δ]`.
-/
@[grind] def lift [ε -< δ] (t : ITree ε α) : ITree δ α :=
  t.map (mapEff ·) mapCont

/-- NOTE: the following instance cannot be defined on `MonadLift`, given that
class's first argument is an `outParam`, so we define `MonadLiftT` directly. -/
instance [ε -< δ] : MonadLiftT (ITree ε) (ITree δ) where
  monadLift := lift

/-!
## Lemmas
-/
section Lemmas

/-! ### Basic -/
section Basic
variable {fEff : ε → δ} {fCont : (i : ε) → κδ (fEff i) → κε i}

@[simp, grind =] theorem map_ret (r : α) :
    map fEff fCont (ret r) = ret r := by
  simp [map]

@[simp, grind =] theorem map_tau (t : ITree ε α) :
    map fEff fCont (tau t) = tau (map fEff fCont t) := by
  conv => {lhs; rw [map]}
  simp

@[simp, grind =] theorem map_vis (i : ε) (k : κε i → ITree ε α) :
    map fEff fCont (vis i k)
    = vis (fEff i) (fun o => (k (fCont i o)).map fEff fCont) := by
  conv => {lhs; rw [map]}
  simp

@[simp, grind =] theorem map_eq_ret_iff (t : ITree ε α) (r : α) :
    map fEff fCont t = ret r ↔ t = ret r := by
  rw [map]; grind

@[simp, grind =] theorem map_eq_tau_iff (t : ITree ε α) :
    map fEff fCont t = tau t' ↔ ∃ u, t = tau u ∧ t' = map fEff fCont u := by
  rw [map]; grind

@[simp, grind =] theorem map_eq_vis_iff (t : ITree ε α) :
    map fEff fCont t = vis i k ↔ ∃ j l,
      t = vis j l
      ∧ i = fEff j
      ∧ k ≍ (fun x => (l (fCont j x)).map fEff fCont) := by
  cases t
  case ret => simp
  case tau => simp
  case vis j l =>
    simp only [map_vis, vis_inj]
    constructor
    · grind
    · rintro ⟨j, l, ⟨rfl, rfl⟩, rfl, rfl⟩
      and_intros <;> rfl


/-- Mapping twice is the same as mapping once with the composed maps. -/
@[simp, grind =] theorem map_map {η κη} [Effect.{u} η κη]
    (fEff₁ : ε → δ) (fCont₁ : (i : ε) → κδ (fEff₁ i) → κε i)
    (fEff₂ : δ → η) (fCont₂ : (i : δ) → κη (fEff₂ i) → κδ i)
    (t : ITree ε α) :
    map fEff₂ fCont₂ (map fEff₁ fCont₁ t)
      = map (fEff₂ <| fEff₁ ·) (fun _ o => fCont₁ _ (fCont₂ _ o)) t := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun (x y : ITree η α) =>
    ∃ (t : ITree ε α),
        x = map fEff₂ fCont₂ (map fEff₁ fCont₁ t)
      ∧ y = map (fEff₂ ∘ fEff₁) (fun i o => fCont₁ i (fCont₂ (fEff₁ i) o)) t)
  · rintro x y ⟨t, rfl, rfl⟩
    cases t with
    | ret r => left; exact ⟨r, by simp, by simp⟩
    | tau u =>
      simp only [map_tau]
      right; left
      exact ⟨_, _, ⟨u, rfl, rfl⟩, rfl, rfl⟩
    | vis i k =>
      simp only [map_vis, Function.comp_apply]
      right; right
      exact ⟨_, _, _, fun o => ⟨_, rfl, rfl⟩, rfl, rfl⟩
  · exact ⟨t, rfl, rfl⟩

/-!
Lift specializations of the basic lemmas. Since `lift` is defined as
`map mapEff mapCont`, these are direct corollaries.
-/
section Lift
variable [ε -< δ]

@[simp, grind =] theorem lift_ret (r : α) :
    lift (ε := ε) (δ := δ) (ret r) = ret r := map_ret _

@[simp, grind =] theorem lift_tau (t : ITree ε α) :
    lift (δ := δ) (tau t) = tau (lift t) := map_tau _

@[simp, grind =] theorem lift_vis (i : ε) (k : κε i → ITree ε α) :
    lift (δ := δ) (vis i k)
    = vis (mapEff i) (fun o => (k (mapCont i o)).lift) := map_vis _ _

@[simp, grind =] theorem lift_eq_ret_iff (t : ITree ε α) (r : α) :
    lift (δ := δ) t = ret r ↔ t = ret r :=
  map_eq_ret_iff ..

@[simp, grind =] theorem lift_eq_tau_iff (t : ITree ε α) (t' : ITree δ α) :
    lift (δ := δ) t = tau t' ↔ ∃ u, t = tau u ∧ t' = lift (δ := δ) u :=
  map_eq_tau_iff ..

@[simp, grind =] theorem lift_eq_vis_iff (t : ITree ε α) (i : δ) (k : κδ i → ITree δ α) :
    lift (δ := δ) t = vis i k ↔ ∃ j l,
      t = vis j l
      ∧ i = mapEff j
      ∧ k ≍ (fun x : κδ _ => (l (mapCont j x)).lift (δ:=δ)) :=
  map_eq_vis_iff ..

end Lift

end Basic

/-! ### Lifting Monadic Ops -/
section Monadic

section Map
variable {fEff : ε → δ} {fCont : (i : ε) → κδ (fEff i) → κε i}

@[simp, grind =] theorem map_pure (r : α) :
    map fEff fCont (pure r : ITree ε _) = pure r := by
  simp

@[simp, grind =]
theorem map_bind {β} (t : ITree ε α) (k : α → ITree ε β) :
    map fEff fCont (t >>= k)
      = map fEff fCont t >>= (fun a => map fEff fCont (k a)) := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun (x y : ITree δ β) =>
    ∃ (α₀ : Type u) (u : ITree ε α₀) (k : α₀ → ITree ε β),
        x = map fEff fCont (u >>= k)
      ∧ y = map fEff fCont u >>= (fun a => map fEff fCont (k a)))
  · rintro x y ⟨α₀, u, k, rfl, rfl⟩
    cases u with
    | tau u' =>
      simp only [tau_bind, map_tau]
      right; left
      exact ⟨_, _, ⟨_, u', k, rfl, rfl⟩, rfl, rfl⟩
    | vis j k'' =>
      simp only [vis_bind, map_vis]
      right; right
      exact ⟨_, _, _, fun o => ⟨_, k'' (fCont j o), k, rfl, rfl⟩, rfl, rfl⟩
    | ret a =>
      simp only [pure_bind, map_pure]
      cases k a with
      | ret r => simp
      | tau t' =>
        simp only [map_tau]
        right; left
        refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => t', ?_⟩, rfl, rfl⟩
        simp
      | vis i k'' =>
        simp only [map_vis]
        right; right
        refine ⟨_, _, _,
                fun o => ⟨_, ret ⟨⟩, fun _ : PUnit => k'' (fCont i o), ?_⟩,
                rfl, rfl⟩
        simp
  · exact ⟨α, t, k, rfl, rfl⟩

end Map

variable [ε -< δ]

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
  simp [lift]

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

theorem mayReturn_map {fEff : ε → δ} {fCont : (i : ε) → κδ (fEff i) → κε i}
    (surj : ∀ i, Function.Surjective (fCont i)) (t : ITree ε α) :
    (map fEff fCont t).MayReturn x ↔ t.MayReturn x := by
  constructor
  · generalize ht : map fEff fCont t = t'
    intro h
    induction h generalizing t
    case ret r _ =>
      replace ht : map fEff fCont t = .ret r := by grind
      obtain rfl : t = .ret r := by simp_all
      grind
    case tau r t' _ hr ih =>
      replace ht : map fEff fCont t = .tau t' := by grind
      obtain ⟨u, rfl, rfl⟩ : ∃ u, t = tau u ∧ t' = map fEff fCont u := by
        simpa using ht
      grind
    case vis r i k o _ hr ih =>
      replace ht : map fEff fCont t = .vis i k := by grind
      obtain ⟨j, l, ⟨rfl, rfl⟩, rfl, rfl⟩ : ∃ j l,
          t = vis j l
          ∧ i = fEff j
          ∧ k ≍ fun x => (l (fCont j x)).map fEff fCont := by
        simpa using ht
      specialize ih (l (fCont j o))
      grind
  · intro h
    induction h
    case ret => grind
    case tau => grind
    case vis t r i k o ht hk hkl =>
      replace ht : t = vis i k := by grind
      subst ht
      obtain ⟨o, rfl⟩ : ∃ o', fCont i o' = o := surj i o
      grind

@[simp, grind =]
theorem mayReturn_lift [ε -< δ] (t : ITree ε α) :
    (lift (δ := δ) t).MayReturn x ↔ t.MayReturn x :=
  mayReturn_map (by grind) t

end MayReturn

/-! ### HasEffect -/
section HasEffect

theorem hasEffect_map {fEff : ε → δ} {fCont : (i : ε) → κδ (fEff i) → κε i}
    (surj : ∀ i, Function.Surjective (fCont i))
    (t : ITree ε α) {e : δ} :
    (map fEff fCont t).HasEffect e ↔
      ∃ e', t.HasEffect e' ∧ fEff e' = e := by
  constructor
  · suffices h : ∀ (t' : ITree δ α) (t : ITree ε α),
        t' = map fEff fCont t → t'.HasEffect e →
        ∃ e', t.HasEffect e' ∧ fEff e' = e by
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
        obtain rfl : fEff i₀ = i' := by grind
        specialize ih (k₀ (fCont i₀ o))
        grind
  · rintro ⟨e', he', rfl⟩
    induction he' with
    | vis_self => grind
    | tau => grind
    | @vis_cont t' j j' k o hu h ih =>
      obtain ⟨o, rfl⟩ : ∃ o', fCont j' o' = o := surj j' o
      grind

@[simp, grind =]
theorem hasEffect_lift [ε -< δ] (t : ITree ε α) {e : δ} :
    (lift (δ:=δ) t).HasEffect e ↔
      ∃ e', t.HasEffect e' ∧ Subeffect.mapEff e' = e :=
  hasEffect_map (by grind) t

end HasEffect

/-! ### Interp -/
section Interp
variable {η κη} [Effect.{u} η κη]

/-- Interpretation composes with `map` -/
@[simp, grind =]
theorem interp_map (fEff : ε → δ) (fCont : (i : ε) → κδ (fEff i) → κε i)
    (f : δ ⤳ ITree η) (t : ITree ε α) :
    interp f (map fEff fCont t)
      = interp (fun i : ε => do
          let x ← f (fEff i)
          return fCont i x
          ) t := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun (x y : ITree η α) =>
    ∃ (α₀ : Type u) (u : ITree η α₀) (k : α₀ → ITree ε α),
        x = u >>= (fun a => interp f (map fEff fCont (k a)))
      ∧ y = u >>= (fun a => interp (fun i : ε => do
          let x ← f (fEff i)
          return fCont i x) (k a)))
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
        simp only [map_tau, interp_tau]
        right; left
        refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => t', ?_⟩, rfl, rfl⟩
        simp
      | vis i k'' =>
        simp only [map_vis, interp_vis, bind_assoc, pure_bind]
        cases f (fEff i) with
        | ret o =>
          simp only [pure_bind]
          right; left
          refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => k'' (fCont i o), ?_⟩, rfl, rfl⟩
          simp
        | tau t' =>
          simp only [tau_bind]
          right; left
          refine ⟨_, _, ⟨_, t', fun x => tau (k'' (fCont i x)), ?_⟩, rfl, rfl⟩
          simp
        | vis j k''' =>
          simp only [vis_bind]
          right; right
          refine ⟨j, _, _,
                  fun o' => ⟨_, k''' o', fun x => tau (k'' (fCont i x)), ?_⟩,
                  rfl, rfl⟩
          simp
  · refine ⟨PUnit, ret ⟨⟩, fun _ => t, ?_⟩
    simp

/-- Interpretation composes with `lift` -/
@[simp, grind =]
theorem interp_lift [ε -< δ] (f : δ ⤳ ITree η) (t : ITree ε α) :
    interp f (lift (δ := δ) t)
      = interp (fun i : ε => do
          let x ← f (Subeffect.mapEff i)
          return Subeffect.mapCont i x
          ) t :=
  interp_map _ _ f t

/--
If `t : ITree ε α` is embedded into `ITree (ε ⊕ δ) α` via `map Sum.inl`,
then interpreting the left component with `f` recovers `interp f t`.
-/
@[simp, grind =]
theorem interpLeft_map_inl (f : ε ⤳ ITree δ) (t : ITree ε α) :
    interpLeft f (map .inl (no_index fun _ o => o) t)
      = interp f t := by
  simp [interpLeft, interp_map]

/--
If `t : ITree δ α` is embedded into `ITree (ε ⊕ δ) α` via `map Sum.inr`,
then interpreting the left component with `f` reinterprets each event of `t`
through the identity handler `Effect.trigger δ`.

Note: the rhs is weakly bisimilar to `t`, but not strongly so,
since `interp` inserts extra `tau`s.
-/
@[simp, grind =]
theorem interpLeft_map_inr (f : ε ⤳ ITree δ) (t : ITree δ α) :
    interpLeft f (map .inr (no_index fun _ o => o) t)
      = interp (Effect.trigger δ) t := by
  simp [interpLeft, interp_map]

end Interp

end Lemmas

end ITree
end ITree
