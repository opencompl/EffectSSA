module

public import ITreeExtras.Definition
public import ITreeExtras.HasEffect

/-!
# ITree `iter` combinator

This file defines `iter`, which inserts an extra `tau` in the recursive case,
making it easier to prove properties about.
-/

@[expose] public section
namespace ITree.ITree
variable {ε} {κ} [Effect.{u} ε κ] {α : Type _}

def iter {α β} (t : α → ITree ε (α ⊕ β)) (a : α) : ITree ε β :=
  (t a) >>= recurse t
partial_fixpoint
where @[grind] recurse (t : α → ITree ε (α ⊕ β)) : α ⊕ β → ITree ε β
  | .inl a => tau <| .iter t a
  | .inr b => return b
  partial_fixpoint

/-!
## Lemmas
-/
section BasicLemmas

@[simp, grind =] theorem iter.recurse_inl {t : α → ITree ε (α ⊕ β)} {a : α} :
    recurse t (.inl a) = (tau <| .iter t a) := by
  rw [recurse]

@[simp, grind =] theorem iter.recurse_inr {t : α → ITree ε (α ⊕ β)} {b : β} :
    recurse t (.inr b) = return b := by
  rw [recurse]

end BasicLemmas

/-!
## Iteration Reachability

`IterReaches f a a'` is the reflexive-transitive closure of the "one iteration
step" relation `(f ·).MayReturn (Sum.inl ·)`. It captures that iterating `f`
starting from `a` can reach a state `a'` where the next call to `f` begins.
-/

inductive IterReaches {α β : Type u} (f : α → ITree ε (α ⊕ β)) : α → α → Prop where
  | refl (a : α) : IterReaches f a a
  | step {a a₁ a' : α} :
      (f a).MayReturn (Sum.inl a₁) → IterReaches f a₁ a' → IterReaches f a a'

attribute [grind .] IterReaches.refl IterReaches.step

/-!
## HasEffect
-/

/--
`iter f a` has effect `e` iff there is some `a'` reachable from `a` by iterating
`f`, such that `f a'` has effect `e`. In other words, effects occur precisely
when some call `f a'` in the iteration chain from `a` carries the effect.
-/
@[simp, grind =]
theorem hasEffect_iter {α β : Type u} {f : α → ITree ε (α ⊕ β)} {a : α} {e : ε} :
    (iter f a).HasEffect e ↔ ∃ a', IterReaches f a a' ∧ (f a').HasEffect e := by
  constructor
  · suffices ∀ (x : ITree ε β), x.HasEffect e →
        ∀ (t' : ITree ε (α ⊕ β)), x = (t' >>= iter.recurse f) →
          t'.HasEffect e
          ∨ (∃ a₁ a', t'.MayReturn (Sum.inl a₁)
                    ∧ IterReaches f a₁ a'
                    ∧ (f a').HasEffect e) by
      intro h
      specialize this (iter f a) h (f a) (by rw [iter])
      grind
    intro x h
    induction h with
    | @vis_self t i k hu =>
      rintro t' rfl
      cases t' with
      | vis => grind
      | tau => grind
      | ret r => cases r <;> simp_all
    | @tau t i t'' ht hi ih =>
      intro t' hx
      replace ht : t = tau t'' := by grind
      subst ht
      cases t' with
      | vis => grind
      | tau t'₀ => grind
      | ret r =>
        cases r with
        | inr => simp_all
        | inl a' =>
          have h₀ : t'' = iter f a' := by simp_all
          subst h₀
          specialize ih (f a') (by rw [iter])
          rcases ih with hfa' | ⟨a₁, a'', hmay, hreach, heff⟩
          · right; exact ⟨a', a', by simp, .refl _, hfa'⟩
          · right; exact ⟨a', a'', by simp, .step hmay hreach, heff⟩
    | @vis_cont t i i' k o ht hk ih =>
      intro t' hx
      replace ht : t = vis i' k := by grind
      subst ht
      cases t' with
      | tau => grind
      | vis i₂ k₂ =>
        obtain ⟨rfl, rfl⟩ : i₂ = i' ∧  k ≍ fun o => k₂ o >>= iter.recurse f := by grind
        grind
      | ret r => cases r <;> (simp_all; grind)
  · rintro ⟨a', hreach, hfa'⟩; induction hreach <;> grind [iter]
