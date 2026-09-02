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

@[simp, grind =] theorem mem_argsSet {v : VarId} {i : Inst ι} :
    v ∈ i.argsSet ↔ v ∈ i.args := VarSet.mem_setOf

@[simp, grind =] theorem mem_resultsSet {v : VarId} {i : Inst ι} :
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

end Lemmas
end Denote
end Inst
