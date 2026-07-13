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
abbrev Effect.Transform (ε) {κ} [Effect ε κ] (m : Type u → Type u) :=
  (i : ε) → m (κ i)
@[inherit_doc] scoped infixr:25 unicode(" ⤳ ", " ~> ") => ITree.Effect.Transform

namespace ITree

variable {ε} {κε} [Effect.{u} ε κε]
         {δ} {κδ} [Effect.{u} δ κδ]
         {ε'} {κε'} [Effect.{u} ε' κε']
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

@[simp, grind =] theorem interp_vis (i : ε) (k : κε i → ITree ε α) :
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
            exact .inl ⟨r, by simp [hva, hz], by simp [hva, hz]⟩
          | tau t' =>
            refine .inr (.inl ⟨t', t', .inl rfl, ?_, ?_⟩)
            · simp [hva, hz]
            · simp [hva, hz]
          | vis i k'' =>
            refine .inr (.inr ⟨i, k'', k'', fun _ => .inl rfl, ?_, ?_⟩)
            · simp [hva, hz]
            · simp [hva, hz]
        | tau t' =>
          refine .inr (.inl ⟨interp f (t' >>= h),
                             interp f t' >>= (fun b => interp f (h b)),
                             ?_, ?_, ?_⟩)
          · exact .inr ⟨PUnit, α₁, ret ⟨⟩, fun _ => t', h, by simp, by simp⟩
          · simp [hva]
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
                               ?_, ?_, ?_⟩)
            · exact .inr ⟨PUnit, α₁, ret ⟨⟩, fun _ => k' o, h, by simp, by simp⟩
            · simp [hva, hfi]
            · simp [hva, hfi]
          | tau t' =>
            refine .inr (.inl ⟨t' >>= (fun o => tau (interp f (k' o >>= h))),
                               t' >>= (fun o => tau (interp f (k' o) >>= fun b => interp f (h b))),
                               ?_, ?_, ?_⟩)
            · exact .inr ⟨_, α₁, t', fun o => tau (k' o), h, by simp, by simp⟩
            · simp [hva, hfi]
            · simp [hva, hfi]
          | vis i' k'' =>
            refine .inr (.inr ⟨i',
                               (fun o' => k'' o' >>= (fun o => tau (interp f (k' o >>= h)))),
                               (fun o' => k'' o' >>= (fun o => tau (interp f (k' o) >>= fun b => interp f (h b)))),
                               ?_, ?_, ?_⟩)
            · intro o'
              exact .inr ⟨_, α₁, k'' o', fun o => tau (k' o), h, by simp, by simp⟩
            · simp [hva, hfi]
            · simp [hva, hfi]
  · exact .inr ⟨PUnit, α, ret ⟨⟩, fun _ => t, k, by simp, by simp⟩

end InterpLemmas

/-! ### Interpreting Sum Effects -/

/--
Given an ITree with events in `ε ⊕ δ`,
interpret only events in `ε` using the handler `f`,
leaving events in `δ` as-is.
-/
def interpLeft (f : ε ⤳ ITree δ) : ITree (ε ⊕ δ) α → ITree δ α :=
  interp (Sum.casesOn · f (Effect.trigger δ))

section InterpLeftLemmas
variable (f : ε ⤳ ITree δ)

/-- `interp_bind` specialized to `interpLeft`. -/
@[simp, grind =]
theorem interpLeft_bind {β} (f : ε ⤳ ITree δ)
    (t : ITree (ε ⊕ δ) α) (k : α → ITree (ε ⊕ δ) β) :
    (t >>= k).interpLeft f = t.interpLeft f >>= (fun a => (k a).interpLeft f) :=
  interp_bind _ t k

/--
When `trigger` targets the left component of `ε ⊕ δ`, `interpLeft` handles
it via the user-provided handler `f`.
-/
@[simp, grind =]
theorem interpLeft_trigger_inl [ε' -< ε] (i : ε') :
    interpLeft f (Effect.trigger (ε₂ := ε ⊕ δ) ε' i)
      = f (Subeffect.map (ε₂ := ε) i).fst
        >>= fun o => tau (return ((Subeffect.map (ε₂ := ε) i).snd o)) := by
  simp [interpLeft, Effect.trigger]

/--
When `trigger` targets the right component of `ε ⊕ δ`, `interpLeft` passes
it through as a `trigger` in `ITree δ`.
-/
@[simp, grind =]
theorem interpLeft_trigger_inr [ε' -< δ] (i : ε') :
    interpLeft f (Effect.trigger (ε₂ := ε ⊕ δ) ε' i)
      = Effect.trigger (ε₂ := δ) ε' i >>= fun o => tau (return o) := by
  simp [interpLeft, Effect.trigger]

end InterpLeftLemmas
