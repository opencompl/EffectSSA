import EffectSSA.Types.WellTyped
import EffectSSA.Types.Simpset
import EffectSSA.Types.Context.Lemmas

/-!
# Lemmas about the typesystem
-/
namespace EffectSSA

/-!
## `grind` lemmas
--------------------------------------------------------------------------------
-/

/-!
### Instruction
-/
namespace Instruction
open Ty.Typ (ptr eff data)
variable {Γ Δ : Context τ}

@[simp, typecheck, grind =]
theorem wellTyped_loadI_iff :
    WellTyped Γ (.loadI t p) Δ ↔ (Γ.isUnrestricted ∧ Γ[p]? = some ptr ∧ Δ = Γ <: t) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_storeI_iff :
    WellTyped Γ (.storeI t p x) Δ
    ↔ (Γ.isUnrestricted ∧ Γ[p]? = some ptr ∧ Γ[x]? = some (data t) ∧ Δ = Γ) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_loadE_iff :
    WellTyped Γ (.loadE t e p) Δ
    ↔ (Γ[e]? = some eff ∧ Γ[p]? = some ptr ∧ Δ = Γ.eraseVar e <: eff <: t) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_storeE_iff :
    WellTyped Γ (.storeE t e p x) Δ
    ↔ (Γ[e]? = some eff ∧ Γ[p]? = some ptr ∧ Γ[x]? = some (data t) ∧ Δ = Γ.eraseVar e <: eff) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_createEff_iff :
    WellTyped Γ .createEff Δ ↔ (Γ.isUnrestricted ∧ Δ = Γ <: eff) := by
  grind [WellTyped]

@[simp, typecheck, grind =]
theorem wellTyped_consumeEff_iff :
    WellTyped Γ (.consumeEff e) Δ
    ↔ (Γ[e]? = some eff ∧ (Γ.eraseVar e).isUnrestricted ∧ Δ = Γ.eraseVar e) := by
  grind [WellTyped]

end Instruction

/-!
### InstructionSeq
-/
namespace InstructionSeq

@[simp, typecheck, grind =]
theorem wellTyped_nil_iff {Γ Δ : Context τ} :
    WellTypedWith Γ .nil Δ ↔ Γ = Δ := by
  grind [WellTypedWith]

@[simp, typecheck, grind =]
theorem wellTyped_cons_iff (i : Instruction τ) (p : InstructionSeq τ) :
    WellTypedWith Γ (i ;> p) Ξ ↔ (∃ Δ, i.WellTyped Γ Δ ∧ p.WellTypedWith Δ Ξ) := by
  grind [WellTypedWith]

end InstructionSeq

/-!
### Program
-/
namespace Program

@[grind =] theorem wellTyped_iff :
    WellTyped Γ ⟨is, vs⟩ ts ↔ ∃ (Δ : Context _),
      ( (Δ.eraseVars vs).isUnrestricted
      ∧ is.WellTypedWith Γ Δ
      ∧ vs.length = ts.length
      ∧ ∀ (i) (hi : i < vs.length), ∃ t,
          ts[i]? = some t ∧ Δ[vs[i]]? = some t) := by
  grind

@[simp, typecheck, grind =]
theorem wellTyped_nil_iff {Γ : Context τ} :
    WellTyped Γ ⟨.nil, vs⟩ ts ↔
      ( (Γ.eraseVars vs).isUnrestricted
      ∧ vs.length = ts.length
      ∧ ∀ (i) (hi : i < vs.length), ∃ t,
          ts[i]? = some t ∧ Γ[vs[i]]? = some t) := by
  grind

end Program

/-!
## Uniqueness of out contexts
--------------------------------------------------------------------------------
-/

@[grind →]
theorem Instruction.WellTyped.unique
    {i : Instruction τ} {Δ Δ' : Context τ}
    (h₁ : i.WellTyped Γ Δ) (h₂ : i.WellTyped Γ Δ') :
      Δ = Δ' := by
  grind [WellTyped]

@[grind →]
theorem InstructionSeq.WellTyped.unique
    {p : InstructionSeq τ} {Δ Δ' : Context τ}
    (h₁ : p.WellTypedWith Γ Δ) (h₂ : p.WellTypedWith Γ Δ') :
      Δ = Δ' := by
  induction p generalizing Γ <;> grind

@[grind →]
theorem Program.WellTyped.unique {p : Program τ}
    (h₁ : p.WellTyped Γ ts) (h₂ : p.WellTyped Γ us) :
      ts = us := by
  rcases h₁ with ⟨Δ₁, h₁, h_un₁, h_ts_len, h_ts⟩
  rcases p with ⟨is, vs⟩
  induction is generalizing Γ
  · apply List.ext_getElem?
    grind
  · grind
