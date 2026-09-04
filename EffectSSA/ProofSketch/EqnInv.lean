module

public import EffectSSA.ProofSketch.Assumptions
public import EffectSSA.ProofSketch.InstSeq
public import EffectSSA.ProofSketch.MultiContext

namespace EffectSSA.ProofSketch
public section

variable [SSA ι σ ν]

/-!
## Main Definitions
-/
@[expose] section Defs

namespace Inst

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

end Inst

/--
TODO: the proof ought to work also with a definition of EqnInv/WellBehaved for
InstSeq that is an analogue of the above for the whole sequence's semantics.
That would be slightly more general, as it allows for a block to be well-behaved
as a whole, even if not each instruction is well-behaved indivually.
For now, though, the simple definition below is good enough.
-/

abbrev InstSeq.EqnInv (is : InstSeq ι) (ρ : SEnv ι) : Prop :=
  ∀ i ∈ is, i.EqnInv ρ

abbrev InstSeq.WellBehaved (is : InstSeq ι) : Prop :=
  ∀ i ∈ is, i.WellBehaved

abbrev Pattern.WellBehaved (P : Pattern ι n) : Prop :=
  ∀ is ∈ P, is.WellBehaved

end Defs

/-!
## Invariance Lemmas
-/
section Invariance
variable {C : MultiContext ι n} {P : Pattern ι n} {is js : InstSeq ι} {i j : Inst ι} {ρ : SEnv ι}

/-! ### Inst -/
namespace Inst

@[grind =>] theorem locals_denote_of_eqnInv (h : i.EqnInv ρ) :
    ∀ x ∈ i.results, (⟦i⟧ ρ).locals x = ρ.locals x := h

/--
If instruction `i` is well-behaved and `js` is well-formed on a context `Γ`
that contains all of `i`'s results and arguments, then `i.EqnInv` is preserved
by executing `js`.
-/
theorem eqnInv_denote_other (h : i.WellBehaved) (hwf : js.WellFormed Γ)
    (hres : i.resultsSet ⊆ Γ) (hargs : i.argsSet ⊆ Γ) :
    i.EqnInv ρ → i.EqnInv (⟦js⟧ ρ) := by
  intro hρ
  induction js generalizing Γ ρ with
  | nil => grind
  | cons j js ih =>
    simp only [InstSeq.denote_cons]
    obtain ⟨_, hdj, hwf'⟩ := InstSeq.wellFormed_cons.mp hwf
    apply ih hwf' (by grind) (by grind) (h.stable _ _ ?_ ?_ hρ)
    · suffices i.resultsSet.Disjoint j.resultsSet by
        simp [VarSet.Disjoint, VarSet.eq_empty_iff] at *
        grind
      grind
    · suffices i.argsSet.Disjoint j.resultsSet by
        simp [VarSet.Disjoint, VarSet.eq_empty_iff] at *
        grind
      grind

end Inst

/-! ### InstSeq -/
namespace InstSeq

@[simp, grind .] theorem eqnInv_nil : EqnInv ([] : InstSeq ι) ρ := by grind
@[simp] theorem eqnInv_cons : (i ;> is).EqnInv ρ ↔ i.EqnInv ρ ∧ is.EqnInv ρ := by grind

@[simp] theorem eqnInv_append :
    (is ++ js).EqnInv ρ ↔ is.EqnInv ρ ∧ js.EqnInv ρ := by
  simp only [EqnInv, List.mem_append]; grind

/--
If `is` is well-behaved and `j` doesn't redefine `is`'s args or results,
then `is.EqnInv` is preserved by executing `j`.
-/
theorem eqnInv_denote_inst (h : is.WellBehaved)
    (hj : ∀ x ∈ j.results, x ∉ is.args ∧ x ∉ is.results) :
    is.EqnInv ρ → is.EqnInv (⟦j⟧ ρ) := by
  intro hρ i hi
  apply (h i hi).stable ρ j ?_ ?_ (hρ i hi)
  · grind
  · suffices i.argsSet.Disjoint j.resultsSet by
      simp [VarSet.Disjoint, VarSet.eq_empty_iff] at *
      grind
    grind

theorem eqnInv_denote_inst_of_wellFormed (h : is.WellBehaved)
    (hj : j.WellFormed Γ) (hΓ : is.results ⊆ Γ ∧ is.args ⊆ Γ) :
    is.EqnInv ρ → is.EqnInv (⟦j⟧ ρ) := by
  apply eqnInv_denote_inst <;> grind

/--
If `is` is well-behaved and `js` is well-formed on a context `Γ` that contains
all of `is`'s results and arguments, then `is.EqnInv` is preserved by executing
`js`.
-/
theorem eqnInv_denote_other (h : is.WellBehaved) (hwf : js.WellFormed Γ)
    (hres : is.results ⊆ Γ) (hargs : is.args ⊆ Γ) :
    is.EqnInv ρ → is.EqnInv (⟦js⟧ ρ) := by
  intro hρ i hi
  apply Inst.eqnInv_denote_other (h i hi) hwf ?_ ?_ (hρ i hi) <;> grind

/--
Evaluating a well-behaved, well-formed instruction sequence yields an environment
that satisfies its own equation invariant.
-/
theorem eqnInv_denote_self (h : is.WellBehaved) (hwf : is.WellFormed Γ) :
    is.EqnInv (⟦is⟧ ρ) := by
  induction is generalizing Γ ρ with
  | nil => grind
  | cons i is ih =>
    simp only [denote_cons, eqnInv_cons]
    obtain ⟨hia, hdj, hwf'⟩ := wellFormed_cons.mp hwf
    refine ⟨?_, ?_⟩
    · exact Inst.eqnInv_denote_other (h i (by grind)) hwf'
        (by grind) (by grind) ((h i (by grind)).idempotent ρ)
    · exact ih (fun j' hj' => h j' (by grind)) hwf'

end InstSeq

end Invariance

/-!
## Locally Pure
Justify the well-behavedness predicate by showing that all so-called
"locally pure" instructions are well-behaved.
-/
section LocallyPure
open Inst

/--
An instruction is *locally pure*, when it's effect on local registers,
is determined purely from the local registers.

To wit: such an instruction is free to modify the *global state* in any way.
-/
@[expose] def Inst.LocallyPure (i : Inst ι) : Prop :=
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
    (wf : i.WellFormed Γ)
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
    have : ∀ y ∈ i.args, η.locals y = ρ.locals y := by
      grind [WellFormed]
    apply locallyPure_imp <;> assumption

end LocallyPure
