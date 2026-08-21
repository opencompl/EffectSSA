module

public import EffectSSA.ProofSketch.ProofSketch

namespace EffectSSA.ProofSketch
public section

variable [SSA ι σ ν]

namespace Inst

/-!
## Axioms
-/
section Axioms

/-!
The semantics of an instruction may depend only on those variable declared
as arguments.
-/
axiom denote_eq_of_args : ∀ i : Inst ι, ∀ ρ η : SEnv ι,
  ρ.state = η.state → (∀ x ∈ i.args, ρ.locals x = η.locals x)
  → ⟦i⟧ ρ = ⟦i⟧ η

end Axioms

/-!
## SSA WellFormedness
-/

/--
An individual instruction is well-formed, when it doesn't use its own result
as an argument.
-/
def WellFormed (i : Inst ι) :=
  ∀ x ∈ i.args, x ∉ i.results

/-!
## Main Definitions
-/

def EqnInv (i : Inst ι) (ρ : SEnv ι) : Prop :=
  ∀ x ∈ i.results,
    (⟦i⟧ ρ).locals x = ρ.locals x

structure WellBehaved (i : Inst ι) where
  stable :
    ∀ ρ, ∀ j : Inst ι,
      (∀ x ∈ i.results, x ∉ j.results)
      → (∀ x ∈ i.args, x ∉ j.results)
      → EqnInv i ρ → EqnInv i (⟦j⟧ ρ)
  idempotent: ∀ ρ, EqnInv i (⟦i⟧ ρ)



/--
An instruction is *purely determined*, when it's effect on local registers
as well how the state is modified, is determined purely from the local registers.
-/
def PurelyDet (i : Inst ι) : Prop :=
  ∀ ρ η, ρ.locals = η.locals →
    (⟦i⟧ ρ).locals = (⟦i⟧ η).locals

theorem purelyDet_imp (i : Inst ι) :
    i.PurelyDet → ∀ ρ η : SEnv ι, (∀ y ∈ i.args, ρ.locals y = η.locals y) →
      ∀ x ∈ i.results, (⟦i⟧ ρ).locals x = (⟦i⟧ η).locals x := by
  intro pu ρ η hy x hx
  let η' : SEnv ι := { ρ with locals := η.locals }
  calc (⟦i⟧ ρ).locals x
    _ = (⟦i⟧ η').locals x := by grind [denote_eq_of_args]
    _ = (⟦i⟧ η).locals x := by grind [PurelyDet]

/--
Every purely determined instruction, is well-behaved.
-/
theorem wellBehaved_of_purelyDet {i : Inst ι}
    (wf : i.WellFormed)
    (pu : i.PurelyDet) :
    i.WellBehaved := by
  constructor
  · -- Stability
    intro ρ j hres harg hρ
    intro x hx
    let η := ⟦j⟧ ρ
    show (⟦i⟧ η).locals x = η.locals x
    suffices (⟦i⟧ η).locals x = (⟦i⟧ ρ).locals x by
      have : x ∉ j.results := by grind
      have : η.locals x = ρ.locals x := by grind
      have : ρ.locals x = (⟦i⟧ ρ).locals x := by grind [EqnInv]
      grind
    have : ∀ y ∈ i.args, η.locals y = ρ.locals y := by grind
    apply purelyDet_imp <;> assumption
  · -- Idempotency
    intro ρ
    intro x hx
    let η := ⟦i⟧ ρ
    show (⟦i⟧ η).locals x = (⟦i⟧ ρ).locals x
    have : ∀ y ∈ i.args, η.locals y = ρ.locals y := by grind [WellFormed]
    apply purelyDet_imp <;> assumption
