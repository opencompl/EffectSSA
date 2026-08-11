module

public import EffectSSA.ProofSketch.ProofSketch

namespace EffectSSA.ProofSketch
public section

namespace Inst

/-!
## Axioms
-/
section Axioms

/-!
The semantics of an instruction may depend only on those variable declared
as arguments.
-/
axiom denote_eq_of_args : ∀ i : Inst, ∀ ρ η : SEnv,
  ρ.state = η.state → (∀ x ∈ i.args, ρ.regs x = η.regs x)
  → ⟦i⟧ ρ = ⟦i⟧ η

end Axioms

/-!
## SSA WellFormedness
-/

/--
An individual instruction is well-formed, when it doesn't use its own result
as an argument.
-/
def WellFormed (i : Inst) :=
  i.args.Disjoint i.results

/-!
## Main Definitions
-/

def EqnInv (i : Inst) (ρ : SEnv) : Prop :=
  ∀ x ∈ i.results,
    (⟦i⟧ ρ).regs x = ρ.regs x

structure WellBehaved (i : Inst) where
  stable :
    ∀ ρ, ∀ j : Inst,
      i.results.Disjoint j.results
      → i.args.Disjoint j.results
      → EqnInv i ρ → EqnInv i (⟦j⟧ ρ)
  idempotent: ∀ ρ, EqnInv i (⟦i⟧ ρ)



/--
An instruction is *purely determined*, when it's effect on local registers
as well how the state is modified, is determined purely from the local registers.
-/
def PurelyDet (i : Inst) : Prop :=
  ∀ ρ η, ρ.regs = η.regs →
    (⟦i⟧ ρ).regs = (⟦i⟧ η).regs

theorem purelyDet_imp (i : Inst) :
    i.PurelyDet → ∀ ρ η : SEnv, (∀ y ∈ i.args, ρ.regs y = η.regs y) →
      ∀ x ∈ i.results, (⟦i⟧ ρ).regs x = (⟦i⟧ η).regs x := by
  intro pu ρ η hy x hx
  let η' : SEnv := ⟨η.regs, ρ.state⟩
  calc (⟦i⟧ ρ).regs x
    _ = (⟦i⟧ η').regs x := by grind [denote_eq_of_args]
    _ = (⟦i⟧ η).regs x := by grind [PurelyDet]

/--
Every purely determined instruction, is well-behaved.
-/
theorem wellBehaved_of_purelyDet {i : Inst}
    (wf : i.WellFormed)
    (pu : i.PurelyDet) :
    i.WellBehaved := by
  constructor
  · -- Stability
    intro ρ j hres harg hρ
    intro x hx
    let η := ⟦j⟧ ρ
    show (⟦i⟧ η).regs x = η.regs x
    suffices (⟦i⟧ η).regs x = (⟦i⟧ ρ).regs x by
      have : x ∉ j.results := by grind
      have : η.regs x = ρ.regs x := by grind
      have : ρ.regs x = (⟦i⟧ ρ).regs x := by grind [EqnInv]
      grind
    have : ∀ y ∈ i.args, η.regs y = ρ.regs y := by grind
    apply purelyDet_imp <;> assumption
  · -- Idempotency
    intro ρ
    intro x hx
    let η := ⟦i⟧ ρ
    show (⟦i⟧ η).regs x = (⟦i⟧ ρ).regs x
    have : ∀ y ∈ i.args, η.regs y = ρ.regs y := by grind [WellFormed]
    apply purelyDet_imp <;> assumption
