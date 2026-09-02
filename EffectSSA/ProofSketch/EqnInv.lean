module

public import EffectSSA.ProofSketch.Assumptions
public import EffectSSA.ProofSketch.ProofSketch

namespace EffectSSA.ProofSketch
public section

variable [SSA ι σ ν]

namespace Inst

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

/-!
## Locally Pure
Justify the well-behavedness predicate by showing that all so-called
"locally pure" instructions are well-behaved.
-/
section LocallyPure

/--
An instruction is *locally pure*, when it's effect on local registers,
is determined purely from the local registers.

To wit: such an instruction is free to modify the *global state* in any way.
-/
@[expose] def LocallyPure (i : Inst ι) : Prop :=
  ∀ ρ η, ρ.locals = η.locals →
    (⟦i⟧ ρ).locals = (⟦i⟧ η).locals

theorem locallyPure_imp (i : Inst ι) :
    i.LocallyPure → ∀ ρ η : SEnv ι, (∀ y ∈ i.args, ρ.locals y = η.locals y) →
      ∀ x ∈ i.results, (⟦i⟧ ρ).locals x = (⟦i⟧ η).locals x := by
  intro pu ρ η hy x hx
  let η' : SEnv ι := { ρ with locals := η.locals }
  calc (⟦i⟧ ρ).locals x
    _ = (⟦i⟧ η').locals x := by have := denote_eq_of_args i ρ η'; grind only
    _ = (⟦i⟧ η).locals x := by grind [LocallyPure]

/--
Every purely determined instruction, is well-behaved.
-/
theorem wellBehaved_of_locallyPure {i : Inst ι}
    (wf : i.WellFormed)
    (pu : i.LocallyPure) :
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
    apply locallyPure_imp <;> assumption
  · -- Idempotency
    intro ρ
    intro x hx
    let η := ⟦i⟧ ρ
    show (⟦i⟧ η).locals x = (⟦i⟧ ρ).locals x
    have : ∀ y ∈ i.args, η.locals y = ρ.locals y := by grind [WellFormed]
    apply locallyPure_imp <;> assumption

end LocallyPure
