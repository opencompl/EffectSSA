module

public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Assumptions

/-!
# Instructions

We assume some type `Inst` of instructions.

-/
public section
namespace EffectSSA.ProofSketch

/-- `Inst` is the type of instructions, with arguments and resulting variable binders. -/
structure Inst (ι : Type) where
  opCode : ι
  args : List VarId
  results : List VarId
  deriving DecidableEq

namespace Inst

/-! ### VarSet Views -/

@[expose] noncomputable def argsSet (i : Inst ι) : VarSet := VarSet.setOf (· ∈ i.args)
@[expose] noncomputable def resultsSet (i : Inst ι) : VarSet := VarSet.setOf (· ∈ i.results)

@[simp, grind =, grind =_] theorem mem_argsSet {v : VarId} {i : Inst ι} :
    v ∈ i.argsSet ↔ v ∈ i.args := VarSet.mem_setOf

@[simp, grind =, grind =_] theorem mem_resultsSet {v : VarId} {i : Inst ι} :
    v ∈ i.resultsSet ↔ v ∈ i.results := VarSet.mem_setOf

/-! ### Straight-line Semantics -/
public section Denote
variable [SSA ι σ ν]

/--
The denotation of an `Inst`struction looks up the values of the declared
arguments from the context `ρ`, then passes it to the denotation of the
contained `opCode`, and updates the environment with the resulting values.
-/
instance : Denote (Inst ι) (SEnv ι → SEnv ι) where
  denote i ρ := SEnv.getD <| do
    let args ← i.args.mapM ρ.locals
    let (state, results) := ⟦i.opCode⟧ ρ.state args
    let locals ← ρ.locals.with? i.results results
    return { ρ with locals, state }

section Lemmas

theorem denote_eq {i : Inst ι} :
    ⟦i⟧ ρ =
      let ρ? : Option (SEnv ι) := do
        let args ← i.args.mapM ρ.locals
        let (state, results) := ⟦i.opCode⟧ ρ.state args
        let locals ← ρ.locals.with? i.results results
        return { ρ with locals, state }
      ρ?.getD { error := true } := by rfl


/-- Instructions only modify the registers in their `results` set. -/
@[grind .] axiom locals_denote_of_not_mem_results (i : Inst ι) {x : VarId} {ρ : SEnv ι}
    (h : x ∉ i.results) : (⟦i⟧ ρ).locals x = ρ.locals x
  -- TODO: ^^ this result should now be provable

/-!
The semantics of an instruction may depend only on those variable declared
as arguments.
-/
theorem denote_eq_of_args : ∀ i : Inst ι, ∀ ρ η : SEnv ι,
    ρ.state = η.state → ρ.error = η.error →
    (∀ x ∈ i.args, ρ.locals x = η.locals x)
    → let ρ' := ⟦i⟧ ρ
      let η' := ⟦i⟧ η
      ρ'.state = η'.state
      ∧ ∀ x ∈ i.results, ρ'.locals x = η'.locals x := by
  rintro i ⟨ℓ₁, s₁, e₁⟩ ⟨ℓ₂, s₂, e₂⟩ rfl rfl hx
  simp only at hx
  have : List.mapM ℓ₂ i.args = List.mapM ℓ₁ i.args := by
    revert hx; induction i.args <;> grind
  simp only [denote_eq, Option.bind_eq_bind, this]
  cases List.mapM ℓ₁ i.args
  · simp
  · rename_i args_vals
    simp only [Option.bind_some]
    obtain ⟨state', rs⟩ := ⟦i.opCode⟧ s₁ args_vals
    simp only [LocalEnv.with?, bne_iff_ne, ne_eq, ite_not, Option.pure_def]
    split
    · simp; grind
    · grind

/--
Each instruction's semantics preserves refinement.
In other words, the semantics are *monotone* w.r.t. the refinement relation.
-/
@[grind .] axiom denote_isRefinedBy_congr {ρ₁ ρ₂ : SEnv ι} (hρ : ρ₁ ⊒ ρ₂) (i : Inst ι) :
    ⟦i⟧ ρ₁ ⊒ ⟦i⟧ ρ₂

end Lemmas
end Denote

/-!
## Wellformedness
-/
section WellFormed
-- TODO: rename to write Well*f*ormed, small f, instead. For now, we wrote
--       `Inst.WellFormed` to keep consistent with `InstSeq.WellFormed`

@[expose, grind] def WellFormed (i : Inst ι) (Γ : VarSet := ∅) : Prop :=
  i.argsSet ⊆ Γ ∧ Γ.Disjoint i.resultsSet

end WellFormed

end Inst
