module

/-!
# Effects

Vendored from the `ITree` library
(https://github.com/ISTA-PLV/coinductive, `ITree/Effect.lean`,
upstream rev `d1aeffe87ec7bd4bd13ed92fdc00ef6c5d58f800`).

Kept verbatim to minimise the maintenance burden of re-syncing with upstream.
-/

@[expose] public section

namespace ITree

class Effect (ε : Type u) (κ : outParam (ε → Type u)) where
  -- class deliberately empty

instance {ε₁ ε₂ : Type u} {κ₁ : ε₁ → Type u} {κ₂ : ε₂ → Type u}
    [Effect ε₁ κ₁] [Effect ε₂ κ₂] : Effect (ε₁ ⊕ ε₂) (Sum.rec κ₁ κ₂) :=
  ⟨⟩

class Subeffect (ε₁ ε₂) {κ₁ : outParam _} {κ₂ : outParam _}
    [Effect.{u} ε₁ κ₁] [Effect.{v} ε₂ κ₂] where
  map : (i₁ : ε₁) → ((i₂ : ε₂) × (κ₂ i₂ → κ₁ i₁))

infix:20 " -< " => Subeffect

instance [Effect ε κ] : ε -< ε where
  map i := ⟨i, λ x => x⟩

instance {ε₁ ε₂ ε' κ₁ κ₂ κ'} [Effect ε₁ κ₁] [Effect ε₂ κ₂] [Effect ε' κ']
    [subl : ε₁ -< ε'] [subr : ε₂ -< ε'] : (ε₁ ⊕ ε₂) -< ε' where
  map
  | .inl x => subl.map x
  | .inr x => subr.map x

instance (priority:=mid) instSubSumL {ε₁ ε₂ ε' κ₁ κ₂ κ'}
    [Effect ε₁ κ₁] [Effect ε₂ κ₂] [Effect ε' κ']
    [sub : ε₁ -< ε₂] : ε₁ -< (ε₂ ⊕ ε') where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inl i, f⟩

instance (priority:=low) instSubSumR {ε₁ ε₂ ε' κ₁ κ₂ κ'}
    [Effect ε₁ κ₁] [Effect ε₂ κ₂] [Effect ε' κ']
    [sub : ε₁ -< ε₂] : ε₁ -< ε' ⊕ ε₂ where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inr i, f⟩
