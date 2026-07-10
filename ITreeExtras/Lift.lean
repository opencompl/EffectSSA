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
  interp' fun i =>
    let ⟨j, k⟩ := Subeffect.map i
    .vis j (.ret ∘ k)

/-- NOTE: the following instance cannot be defined on `MonadLift`, given that
class's first argument is an `outParam`, so we define `MonadLiftT` directly. -/
instance [ε -< δ] : MonadLiftT (ITree ε) (ITree δ) where
  monadLift := lift

section Lemmas

/-! #### `liftM` -/

@[simp, grind =]
theorem hasEffect_liftM
    {ε₁ ε₂} {κ₁ : ε₁ → Type _} {κ₂ : ε₂ → Type _}
    [Effect ε₁ κ₁] [Effect ε₂ κ₂] [ε₁ -< ε₂]
    (t : ITree ε₁ α) {e : ε₂} :
    (liftM (n:=ITree ε₂) t).HasEffect e ↔
      ∃ e', t.HasEffect e' ∧ (Subeffect.map e').fst = e := by
  sorry

@[simp, grind =]
theorem mayReturn_liftM
    {ε₁ ε₂} {κ₁ : ε₁ → Type _} {κ₂ : ε₂ → Type _}
    [Effect ε₁ κ₁] [Effect ε₂ κ₂] [ε₁ -< ε₂]
    (t : ITree ε₁ α) :
    (liftM (n:=ITree ε₂) t).MayReturn x ↔ t.MayReturn x := by
  sorry

end Lemmas

end ITree
end ITree
