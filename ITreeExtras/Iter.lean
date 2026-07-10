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
## HasEffect
-/

@[grind →]
theorem hasEffect_iter {α β : Type u} {f : α → ITree ε (α ⊕ β)} {a : α} :
    (iter f a).HasEffect e → ∃ b, (f b).HasEffect e := by
  suffices
    ∀ (x : ITree ε β) (t' : ITree ε (α ⊕ β)),
      x = (t' >>= iter.recurse f) →
      x.HasEffect e →
        t'.HasEffect e
        ∨ ∃ b, (f b).HasEffect e
  by
    specialize this (iter f a) (f a) <| by rw [iter]
    grind
  intro x t' hx h
  induction h generalizing t'
  case vis_self i k hu =>
    subst hx
    cases t' with
    | vis => grind
    | tau => grind
    | ret r => cases r <;> simp_all
  case tau t i t'' ht hi  ih =>
    replace ht : t = tau t'' := by grind
    subst ht
    cases t' with
    | vis => grind
    | tau => grind
    | ret r =>
      cases r with
      | inr => simp_all
      | inl a' =>
        replace hx : t'' = iter f a' := by simp_all
        subst hx
        specialize ih (f a') <| by rw [iter]
        cases ih <;> grind
  case vis_cont t i i' k e ht hk ih =>
    replace ht : t = vis i' k := by grind
    subst ht
    cases t'
    case tau => grind
    case vis i'' k' => grind
    case ret r =>
      cases r with
      | inl => grind
      | inr => simp only [pure_eq_ret, bind_ret, iter.recurse_inr] at hx; grind
