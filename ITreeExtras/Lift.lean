module

public import ITreeExtras.Definition
public import ITreeExtras.InterpM
public import ITreeExtras.Basic

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
  interpM fun i =>
    let ⟨j, k⟩ := Subeffect.map i
    .vis j (.ret ∘ k)

/-- NOTE: the following instance cannot be defined on `MonadLift`, given that
class's first argument is an `outParam`, so we define `MonadLiftT` directly. -/
instance [ε -< δ] : MonadLiftT (ITree ε) (ITree δ) where
  monadLift := lift

end ITree
end ITree
