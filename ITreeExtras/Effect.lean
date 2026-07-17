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

instance {ε₁ ε₂} {κ₁ κ₂} [Effect.{u} ε₁ κ₁] [Effect.{u} ε₂ κ₂] :
    Effect (ε₁ ⊕ ε₂) (Sum.rec κ₁ κ₂) :=
  ⟨⟩

class Subeffect (ε₁ ε₂) {κ₁ : outParam _} {κ₂ : outParam _}
    [Effect.{u} ε₁ κ₁] [Effect.{v} ε₂ κ₂] where
  map : (i₁ : ε₁) → ((i₂ : ε₂) × (κ₂ i₂ → κ₁ i₁))
  map_surj : ∀ i₁, Function.Surjective (map i₁).snd := by
    grind [Function.Surjective]

infix:20 " -< " => Subeffect
attribute [grind! .] Subeffect.map_surj

/-! ## Subeffect Definitions -/
namespace Subeffect
variable [Effect ε κ] [Effect ε' κ'] [Effect ε₁ κ₁] [Effect ε₂ κ₂]

/-- `mapEff` is an abbreviation of the first component of `map`. -/
@[simp, grind] abbrev mapEff [ε₁ -< ε₂] (i₁ : ε₁) : ε₂ :=
  (map i₁).1

/-- `mapCont` is an abbreviation of the second component of `map`. -/
@[simp, grind] abbrev mapCont [ε₁ -< ε₂] (i₁ : ε₁) : κ₂ (mapEff i₁) → κ₁ i₁ :=
  (map i₁).2

/-! ## Instances -/

/-! ### Identity / Reflexivity -/
section Refl

/-- Every effect is a sub-effect of itself. -/
instance : ε -< ε where
  map i := ⟨i, λ x => x⟩

@[simp, grind =] theorem map_eq_self (i : ε) :
    (map (ε₂ := ε) i) = ⟨i, id⟩ := rfl
@[simp, grind =] theorem mapEff_eq_self (i : ε) :
    (mapEff (ε₂ := ε) i) = i := rfl

end Refl

/-! ### Sum Effects -/
section Sum

/-!
If both `ε₁` and `ε₂` are sub-effects of `ε'`,
then `ε₁ ⊕ ε₂` is a sub-effect of `ε'`,
via a straightforward case-analysis.
-/
instance [subl : ε₁ -< ε'] [subr : ε₂ -< ε'] : (ε₁ ⊕ ε₂) -< ε' where
  map
  | .inl x => subl.map x
  | .inr x => subr.map x
  map_surj i₁ := by cases i₁ <;> apply Subeffect.map_surj

@[simp, grind =] theorem map_inl [ε₁ -< ε'] [ε₂ -< ε'] {e : ε₁} :
    (map (ε₁ := ε₁ ⊕ ε₂) (ε₂:=ε') <| .inl e) = map e := rfl
@[simp, grind =] theorem mapEff_inl [ε₁ -< ε'] [ε₂ -< ε'] {e : ε₁} :
    (mapEff (ε₁ := ε₁ ⊕ ε₂) (ε₂:=ε') <| .inl e) = mapEff e := rfl
@[simp, grind =] theorem map_inr [ε₁ -< ε'] [ε₂ -< ε'] {e : ε₂} :
    (map (ε₁ := ε₁ ⊕ ε₂) (ε₂:=ε') <| .inr e) = map e := rfl
@[simp, grind =] theorem mapEff_inr [ε₁ -< ε'] [ε₂ -< ε'] {e : ε₂} :
    (mapEff (ε₁ := ε₁ ⊕ ε₂) (ε₂:=ε') <| .inr e) = mapEff e := rfl

/-- `ε₁` is a sub-effect of `ε₁ ⊕ ε₂`. -/
instance (priority:=mid) instSubSumL [sub : ε₁ -< ε₂] : ε₁ -< (ε₂ ⊕ ε') where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inl i, f⟩

/-- The `ε' -< (ε₁ ⊕ ε₂)` instance derived from `ε' -< ε₁` maps to `Sum.inl`. -/
@[simp, grind =] theorem map_eq_inl [ε' -< ε₁] (e : ε') :
    map (ε₂ := ε₁ ⊕ ε₂) e = ⟨.inl (map e).fst, (map e).snd⟩ := rfl
@[simp, grind =] theorem mapEff_eq_inl [ε' -< ε₁] (e : ε') :
    mapEff (ε₂ := ε₁ ⊕ ε₂) e = .inl (mapEff e) := rfl

/-- `ε₂` is a sub-effect of `ε₁ ⊕ ε₂`. -/
instance (priority:=low) instSubSumR {ε₁ ε₂ ε' κ₁ κ₂ κ'}
    [Effect ε₁ κ₁] [Effect ε₂ κ₂] [Effect ε' κ']
    [sub : ε₁ -< ε₂] : ε₁ -< ε' ⊕ ε₂ where
  map t := let ⟨i, f⟩ := (sub.map t); ⟨.inr i, f⟩

/-- The `ε' -< (ε₁ ⊕ ε₂)` instance derived from `ε' -< ε₂` maps to `Sum.inr`. -/
@[simp, grind =] theorem map_eq_inr [ε' -< ε₂] (e : ε') :
    map (ε₂ := ε₁ ⊕ ε₂) e = ⟨.inr (map e).fst, (map e).snd⟩ := rfl
@[simp, grind =] theorem mapEff_eq_inr [ε' -< ε₂] (e : ε') :
    mapEff (ε₂ := ε₁ ⊕ ε₂) e = .inr (mapEff e) := rfl
