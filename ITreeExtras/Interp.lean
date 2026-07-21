module

public import ITreeExtras.Definition
public import ITreeExtras.Basic
public import ITreeExtras.Bisim
public import ITreeExtras.Iter

/-!
# ITree Interpretation

This file defines `ITree.interp`, the interpretation of the effects of an ITree
into an ITree with different effects.

This definition differs from the original, in that an extra `tau` is inserted,
by our use of modified `tau`.
-/

@[expose] public section
namespace ITree

/-- Notation for effect handlers targeting a monad `m`. -/
abbrev Effect.Transform {ι : Type u} (ε : ι → Type u) (m : Type u → Type u) :=
  (i : ι) → m (ε i)
@[inherit_doc] scoped infixr:25 unicode(" ⤳ ", " ~> ") => ITree.Effect.Transform

namespace ITree

variable {ι : Type u} {ε : ι → Type u}
         {ιδ : Type u} {δ : ιδ → Type u}
         {ιε' : Type u} {ε' : ιε' → Type u}
         {α}

/--
Interpret an `ITree ε α` into an `ITree` with a different type of effects `δ`.

See also `ITree.interpM` for an alternative which interprets effects into a
generic monad `m`.
-/
def interp (f : ε ⤳ ITree δ) : ITree ε α → ITree δ α :=
  iter fun t =>
    match t.unfold with
    | .ret r => return (.inr r)
    | .tau t => return (.inl t)
    | .vis i k => do
        let o ← f i
        return (.inl (k o))

section InterpLemmas
variable (f : ε ⤳ ITree δ)

@[simp, grind =] theorem interp_ret (r : α) :
    interp f (ret r) = ret r := by
  unfold interp iter
  simp

@[simp, grind =] theorem interp_pure (r : α) :
    interp f (pure r) = pure r := by
  simp

@[simp, grind =] theorem interp_tau (t : ITree ε α) :
    interp f (tau t) = tau (interp f t) := by
  unfold interp
  rw (occs := [1]) [iter]
  simp

@[simp, grind =] theorem interp_vis (i : ι) (k : ε i → ITree ε α) :
    interp f (vis i k) = f i >>= fun o => tau (interp f (k o)) := by
  unfold interp
  rw (occs := [1]) [iter]
  simp

@[simp, grind =] theorem interp_eq_ret_iff (t : ITree ε α) (r : α) :
    interp f t = ret r ↔ t = ret r := by
  cases t with
  | ret => simp
  | tau => simp
  | vis i k =>
    suffices interp f (vis i k) ≠ ret r by grind
    grind

@[simp, grind =]
theorem interp_bind {β} (t : ITree ε α) (k : α → ITree ε β) :
    interp f (t >>= k) = interp f t >>= (fun a => interp f (k a)) := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun (x y : ITree δ β) =>
    x = y
    ∨ ∃ (α₀ α₁ : Type u) (u : ITree δ α₀)
        (v : α₀ → ITree ε α₁) (h : α₁ → ITree ε β),
        x = u >>= (fun a => interp f (v a >>= h))
      ∧ y = u >>= (fun a => interp f (v a) >>= fun b => interp f (h b)))
  · rintro x y (rfl | ⟨α₀, α₁, u, v, h, rfl, rfl⟩)
    · cases x with
      | ret r => exact .inl ⟨r, rfl, rfl⟩
      | tau t' => exact .inr (.inl ⟨t', t', .inl rfl, rfl, rfl⟩)
      | vis i k'' => exact .inr (.inr ⟨i, k'', k'', fun _ => .inl rfl, rfl, rfl⟩)
    · cases u with
      | tau u' =>
        refine .inr (.inl ⟨u' >>= (fun a => interp f (v a >>= h)),
                           u' >>= (fun a => interp f (v a) >>= fun b => interp f (h b)),
                           ?_, ?_, ?_⟩)
        · exact .inr ⟨α₀, α₁, u', v, h, rfl, rfl⟩
        · simp
        · simp
      | vis i k'' =>
        refine .inr (.inr ⟨i,
                           (fun o => k'' o >>= (fun a => interp f (v a >>= h))),
                           (fun o => k'' o >>= (fun a => interp f (v a) >>= fun b => interp f (h b))),
                           ?_, ?_, ?_⟩)
        · intro o
          exact .inr ⟨α₀, α₁, k'' o, v, h, rfl, rfl⟩
        · simp
        · simp
      | ret a =>
        cases hva : v a with
        | ret b =>
          -- x = y = interp f (h b); case on its top-level structure.
          cases hz : interp f (h b) with
          | ret r =>
            refine .inl ⟨r, ?_⟩
            simp [hva, hz]
          | tau t' =>
            refine .inr (.inl ⟨t', t', .inl rfl, ?_⟩)
            simp [hva, hz]
          | vis i k'' =>
            refine .inr (.inr ⟨i, k'', k'', fun _ => .inl rfl, ?_⟩)
            simp [hva, hz]
        | tau t' =>
          refine .inr (.inl ⟨interp f (t' >>= h),
                             interp f t' >>= (fun b => interp f (h b)),
                             ?_, ?_⟩)
          · exact .inr ⟨PUnit, α₁, ret ⟨⟩, fun _ => t', h, by simp, by simp⟩
          · simp [hva]
        | vis i k' =>
          -- After simplification:
          -- x = f i >>= fun o => tau (interp f (k' o >>= h))
          -- y = f i >>= fun o => tau (interp f (k' o) >>= fun b => interp f (h b))
          -- We case on f i to determine Bisim step.
          cases hfi : f i with
          | ret o =>
            refine .inr (.inl ⟨interp f (k' o >>= h),
                               interp f (k' o) >>= (fun b => interp f (h b)),
                               ?_, ?_⟩)
            · exact .inr ⟨PUnit, α₁, ret ⟨⟩, fun _ => k' o, h, by simp, by simp⟩
            · simp [hva, hfi]
          | tau t' =>
            refine .inr (.inl ⟨t' >>= (fun o => tau (interp f (k' o >>= h))),
                               t' >>= (fun o => tau (interp f (k' o) >>= fun b => interp f (h b))),
                               ?_, ?_⟩)
            · exact .inr ⟨_, α₁, t', fun o => tau (k' o), h, by simp, by simp⟩
            · simp [hva, hfi]
          | vis i' k'' =>
            refine .inr (.inr ⟨i',
                               (fun o' => k'' o' >>= (fun o => tau (interp f (k' o >>= h)))),
                               (fun o' => k'' o' >>= (fun o => tau (interp f (k' o) >>= fun b => interp f (h b)))),
                               ?_, ?_⟩)
            · intro o'
              exact .inr ⟨_, α₁, k'' o', fun o => tau (k' o), h, by simp, by simp⟩
            · simp [hva, hfi]
  · exact .inr ⟨PUnit, α, ret ⟨⟩, fun _ => t, k, by simp, by simp⟩

@[simp]
theorem interp_seqRight {β} (t : ITree ε α) (u : ITree ε β) :
    interp f (t *> u) = interp f t *> interp f u := by
  simp [seqRight_eq_bind]

@[simp, grind =]
theorem interp_forM {γ} (xs : List γ) (g : γ → ITree ε PUnit) :
    interp f (forM xs g) = forM xs (fun a => interp f (g a)) := by
  induction xs <;> simp [*]

end InterpLemmas

/--
Interpretation composes: interpreting `t` through `g` then `h` is the same as
interpreting `t` through the pointwise composition `interp h ∘ g`.
-/
@[simp, grind =]
theorem interp_interp {ιη : Type u} {η : ιη → Type u}
    (g : ε ⤳ ITree δ) (h : δ ⤳ ITree η) (t : ITree ε α) :
    interp h (interp g t) = interp (fun i => interp h (g i)) t := by
  apply eq_of_bisim
  apply Bisim.coinduct (fun (x y : ITree η α) =>
    ∃ (α₀ : Type u) (u : ITree η α₀) (k : α₀ → ITree ε α),
        x = u >>= (fun a => interp h (interp g (k a)))
      ∧ y = u >>= (fun a => interp (fun i => interp h (g i)) (k a)))
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
      | ret r =>
        simp only [interp_pure]
        left
        exact ⟨r, rfl, rfl⟩
      | tau t' =>
        simp only [interp_tau]
        right; left
        refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => t', ?_⟩, rfl, rfl⟩
        simp
      | vis i k'' =>
        simp only [interp_vis, interp_bind, interp_tau]
        cases interp h (g i) with
        | ret o =>
          simp only [pure_bind]
          right; left
          refine ⟨_, _, ⟨_, ret ⟨⟩, fun _ : PUnit => k'' o, ?_⟩, rfl, rfl⟩
          simp
        | tau t' =>
          simp only [tau_bind]
          right; left
          refine ⟨_, _, ⟨_, t', fun o => tau (k'' o), ?_⟩, rfl, rfl⟩
          simp
        | vis j' k''' =>
          simp only [vis_bind]
          right; right
          refine ⟨j', _, _, fun o' => ⟨_, k''' o', fun o => tau (k'' o), ?_⟩, rfl, rfl⟩
          simp
  · refine ⟨PUnit, ret ⟨⟩, fun _ => t, ?_⟩; simp

/-! ### Interpreting Sum Effects -/

/--
Given an ITree with events in `ε ⊕ₑ δ`,
interpret only events in `ε` using the handler `f`,
leaving events in `δ` as-is.
-/
def interpLeft (f : ε ⤳ ITree δ) : ITree (ε ⊕ₑ δ) α → ITree δ α :=
  interp (Sum.casesOn · f (Effect.trigger δ))

section InterpLeftLemmas
variable (f : ε ⤳ ITree δ)

/-! ### monadic -/

/-- `interp_bind` specialized to `interpLeft`. -/
@[simp, grind =]
theorem interpLeft_bind {β} (t : ITree (ε ⊕ₑ δ) α) (k : α → ITree (ε ⊕ₑ δ) β) :
    (t >>= k).interpLeft f = t.interpLeft f >>= (fun a => (k a).interpLeft f) :=
  interp_bind _ t k

@[simp]
theorem interpLeft_seqRight {β} (t : ITree (ε ⊕ₑ δ) α) (u : ITree (ε ⊕ₑ δ) β) :
    interpLeft f (t *> u) = interpLeft f t *> interpLeft f u := by
  simp [seqRight_eq_bind]

/-- `interp_forM` specialized to `interpLeft`. -/
@[simp, grind =]
theorem interpLeft_forM {γ} (f : ε ⤳ ITree δ)
    (xs : List γ) (g : γ → ITree (ε ⊕ₑ δ) PUnit) :
    (forM xs g).interpLeft f = forM xs (fun a => (g a).interpLeft f) :=
  interp_forM _ xs g

/-! ### trigger -/

/--
When `trigger` targets the left component of `ε ⊕ₑ δ`, `interpLeft` handles
it via the user-provided handler `f`.
-/
@[simp, grind =]
theorem interpLeft_trigger_inl [ε' -< ε] (i : ιε') :
    interpLeft f (Effect.trigger (ε₂ := ε ⊕ₑ δ) ε' i)
      = f (Subeffect.map (ε₁ := ε') (ε₂ := ε) i).fst
        >>= fun o => tau (return ((Subeffect.map (ε₁ := ε') (ε₂ := ε) i).snd o)) := by
  simp [interpLeft, Effect.trigger]

/--
When `trigger` targets the right component of `ε ⊕ₑ δ`, `interpLeft` passes
it through as a `trigger` in `ITree δ`.
-/
@[simp, grind =]
theorem interpLeft_trigger_inr [ε' -< δ] (i : ιε') :
    interpLeft f (Effect.trigger (ε₂ := ε ⊕ₑ δ) ε' i)
      = Effect.trigger (ε₂ := δ) ε' i >>= fun o => tau (return o) := by
  simp [interpLeft, Effect.trigger]

end InterpLeftLemmas
