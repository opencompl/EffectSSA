module

public import EffectSSA.ProofSketch.Assumptions
public import EffectSSA.ProofSketch.Notation.Refinement
public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.InstSeq
public import EffectSSA.ProofSketch.Pattern
public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.Effect
public import EffectSSA.ProofSketch.CFG
public import EffectSSA.ProofSketch.Prec

/-!
# Contextual Equivalence Proof Sketch

This file contains a stand-alone proof sketch that denotational equivalence
implies contextual equivalence, in an SSA-based rewriting setting.

-/

@[expose] public noncomputable section
namespace EffectSSA.ProofSketch

variable [SSA ι σ ν]

/-!
## Equation Lemma
-/
section EqnLemma

def Inst.EqnLemma (i : Inst ι) (x : VarId) (ρ : SEnv ι) : Prop :=
  x ∈ i.results → (⟦i⟧ ρ).locals x = ρ.locals x

@[grind] def InstSeq.EqnLemma (is : InstSeq ι) (x : VarId) (ρ : SEnv ι) : Prop :=
  ∀ i ∈ is, Inst.EqnLemma i x ρ

@[grind] def Pattern.EqnLemma (I : Pattern ι n) (x : VarId) (ρ : SEnv ι) : Prop :=
  ∀ i ∈ I, InstSeq.EqnLemma i x ρ

-- TODO: HasEqn should probably be called WellBehaved or some such

/--
We say that an instruction `i` has a well-behaved equation lemma when:

* validity of the equation lemma is stable under the execution of more instructions, and
* executing `i` is guaranteed to yield an environment that satisfies its
  own equation lemma
-/
structure Inst.HasEqn (i : Inst ι) : Prop where
  stable : ∀ x ρ, Inst.EqnLemma i x ρ → ∀ j : Inst ι, x ∉ j.results → Inst.EqnLemma i x (⟦j⟧ ρ)
  idempotent : ∀ x ρ, Inst.EqnLemma i x (⟦i⟧ ρ)

@[grind] def InstSeq.HasEqn (is : InstSeq ι) : Prop :=
  ∀ i ∈ is, Inst.HasEqn i

@[grind] def Pattern.HasEqn (I : Pattern ι n) : Prop :=
  ∀ i ∈ I, InstSeq.HasEqn i

section Lemmas
variable {i : Inst ι} {is : InstSeq ι} {I : Pattern ι n}

/-! vacuous -/

@[grind =>] theorem Inst.eqnLemma_of_not_mem_results {ρ : SEnv ι} (hx : x ∉ i.results) :
    EqnLemma i x ρ := by
  grind [EqnLemma]

@[grind =>] theorem InstSeq.eqnLemma_of_not_mem_results {ρ : SEnv ι} (hx : x ∉ is.results) :
    EqnLemma is x ρ := by
  intro i hi
  grind

@[grind =>] theorem Pattern.eqnLemma_of_not_mem_results {ρ : SEnv ι} (hx : x ∉ I.results) :
    EqnLemma I x ρ := by
  intro is his
  grind

/-! structural lemmas -/
variable (I : Pattern ι n) (is : InstSeq ι)

@[simp, grind .] theorem InstSeq.EqnLemma_nil {ρ : SEnv ι} :
    InstSeq.EqnLemma ([] : InstSeq ι) x ρ := by
  grind [InstSeq.EqnLemma]

@[simp, grind =] theorem InstSeq.EqnLemma_cons {i : Inst ι} {is : InstSeq ι} {ρ : SEnv ι} :
    InstSeq.EqnLemma (i ;> is) x ρ ↔ Inst.EqnLemma i x ρ ∧ InstSeq.EqnLemma is x ρ := by
  grind [InstSeq.EqnLemma]

variable {I} in
@[grind .]
theorem Pattern.eqnLemma_of_mem_results_get {k : Nat} {hk} {ρ : SEnv ι}
    (hx : x ∈ I[k].results) (wf : I.NoShadowing):
    Pattern.EqnLemma I x ρ ↔ InstSeq.EqnLemma I[k] x ρ := by
  generalize hi : I[k] = is
  constructor
  · grind
  · intro h js hj
    by_cases is = js; grind
    by_cases x ∈ is.results
    · have : x ∉ js.results := by
        have := results_disjoint_of_mem_of_noShadowing (by grind : is ∈ I) hj
        grind
      grind
    · grind

/-! stability -/

attribute [grind =>] Inst.HasEqn.stable

/--
If `is.HasEqn`, then validity of the equation lemma is stable under the execution
another instruction `j`.
-/
@[grind =>]
theorem InstSeq.eqnLemma_of_eqnLemma_inst {ρ : SEnv ι} (hEqn : HasEqn is) :
    EqnLemma is x ρ → ∀ j : Inst ι, x ∉ j.results → EqnLemma is x (⟦j⟧ ρ) := by
  grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another instruction `j`.
-/
@[grind =>]
theorem Pattern.eqnLemma_of_eqnLemma_inst {ρ : SEnv ι} (hEqn : HasEqn I) :
    EqnLemma I x ρ → ∀ j : Inst ι, x ∉ j.results → EqnLemma I x (⟦j⟧ ρ) := by
  grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Pattern.eqnLemma_of_eqnLemma_instSeq {ρ : SEnv ι} (hI : HasEqn I) :
    EqnLemma I x ρ → ∀ js : InstSeq ι, x ∉ js.results → EqnLemma I x (⟦js⟧ ρ) := by
  intro heqn js hjs
  induction js generalizing ρ
  · exact heqn
  · grind

/--
If `i.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Inst.eqnLemma_of_eqnLemma_instSeq {i : Inst ι} {ρ : SEnv ι} (hi : HasEqn i) :
    EqnLemma i x ρ → ∀ js : InstSeq ι, x ∉ js.results → EqnLemma i x (⟦js⟧ ρ) := by
  intro heqn js hjs
  induction js generalizing ρ
  · exact heqn
  · grind

/-! denote lemmas -/

@[grind =] theorem Inst.locals_denote_of_eqnLemma {i : Inst ι} {ρ : SEnv ι}
    (h : EqnLemma i x ρ) : (⟦i⟧ ρ).locals x = ρ.locals x := by
  grind [EqnLemma]

@[grind .] theorem InstSeq.locals_denote_of_eqnLemma {is : InstSeq ι} {ρ : SEnv ι}
    (hEqn : HasEqn is)
    (hwf : is.NoShadowing) (h : EqnLemma is x ρ) :
    (⟦is⟧ ρ).locals x = ρ.locals x := by
  induction is generalizing ρ
  · rfl
  · grind

/-! idempotence -/

attribute [grind .] Inst.HasEqn.idempotent

/--
If `is.HasEqn`, then evaluating `is` is guaranteed to yield an environment which
satisfies its own equation lemma at any variable.
-/
@[grind =>]
theorem InstSeq.eqnLemma_denote_self {is : InstSeq ι} (hEqn : HasEqn is)
    (hwf : is.NoShadowing) (ρ) :
    EqnLemma is x (⟦is⟧ ρ) := by
  induction is generalizing ρ
  · simp
  · simp; grind

end Lemmas

section EqnLemmaUpTo

/--
`I.usesAt v` is an alias of `I.collapse.usesAt v`.

See `InstSeq.usesAt` for details.
-/
abbrev Pattern.usesAt (v : VarId) (I : Pattern ι n) := I.collapse.usesAt v

/--
`I.getDef? v` is an alias of `I.collapse.getDef? v`.

See `InstSeq.getDef?` for details.
-/
abbrev Pattern.getDef? (v : VarId) (I : Pattern ι n) :=
  I.collapse.getDef? v

/--
`I.EqnLemmaUpTo h ρ` holds when `ρ` satisfies the equation lemma for all
(transitive) dependencies of the `h`-th pattern of `I`.
-/
def Pattern.EqnLemmaUpTo (I : Pattern ι n) (h : Hole n) (ρ : SEnv ι) : Prop :=
  ∀ x ∈ I[h].args,
    ∀ y, y = x ∨ y ∈ (I.usesAt x) → Pattern.EqnLemma I y ρ

end EqnLemmaUpTo
end EqnLemma

/-!
## Denotational Refinement & Equivalence
-/
section Denotational

/--
A pattern `I` is denotationally refined by pattern `J`,
when for any hole `h` and environments such that `ρ ⊒ η` and
`ρ` (resp `η`) satisfies the equation lemma for all (transitive) dependencies
of the `h`-th sequence of `I` (resp `J`), it is the case that the denotation of
`h`-th of `I` under `ρ` is refined by the denotation of the `h`-th hole of `J`
under `η`.

TODO: We ought to prove that this condition is actually implied by the much more
simple `⟦I⟧ ρ ⊒ ⟦J⟧ ρ` with some side-condition on the variables of each pattern
in `I` and `J`.
-/
def Pattern.DenRefine (I J : Pattern ι n) : Prop :=
  ∀ h : Hole n, ∀ ρ η, ρ ⊒ η →
    I.EqnInvUpTo h ρ →
    J.EqnInvUpTo h η →
    ⟦ I[h] ⟧ ρ ⊒ ⟦ J[h] ⟧ η

-- Sanity check: we should check/proof that denrefine is at least reflexive,
-- but it likely should be a pre-order (not quite partial, because antisymmetry is
-- probably broken, but that can be fixed w/ quotients)

end Denotational

/-!
## Contextual Refinement
-/

/--
A pattern `I` is contextually refined by pattern `J`,
when for any complete context `C` such that `C[I]` and `C[J]` are both
wellformed, `C[I]` is (denotationally) refined by `C[J]`.
-/
def Pattern.CtxRefine (I J : Pattern ι n) : Prop :=
  ∀ (C : MultiContext ι n), C.Complete →
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed ∅ → CJ.WellFormed ∅ →
      ⟦CI⟧ {} ⊒ ⟦CJ⟧ {}

/-!
## Residual
-/
section Residual

/--
We say that `Γ` is a residual of context `C` under pattern `I` when

TODO: dedup with Invariant
-/
@[grind, grind cases]
private structure Residual (Γ : VarSet) (C : MultiContext ι n) (P : Pattern ι n) : Prop where
  /-- `H` is the list of previously seen holes -/
  residual : ∃ H : List (Hole n), C.CompleteMod H ∧ ∀ h ∈ H, P[h].results ⊆ Γ
  /-- `C.plug I` is well-formed with free variables `Γ`. -/
  wf : (C.plug P).WellFormed Γ

namespace Residual
variable {Γ : VarSet} {C : MultiContext ι n} {P : Pattern ι n} {i : Inst ι} {h : Hole n}

/-! invariants -/

private theorem initial (wf : (C.plug P).WellFormed ∅) (hC : C.Complete) : Residual ∅ C P := by
  grind [Pattern.mem_iff_getElem_hole, MultiContext.CompleteMod]

@[grind →] private theorem of_cons_inst :
    Residual Γ (.inl i :: C) P → Residual (i.resultsSet ∪ Γ) C P := by
  rintro ⟨wf, residual⟩;
  constructor
  · simp_all; grind
  · simp_all

@[grind →] private theorem of_cons_hole  :
    Residual Γ (.inr h :: C) P → Residual (P[h].results ∪ Γ) C P := by
  rintro ⟨wf, residual⟩; constructor
  · simp_all; grind
  · simp_all

end Residual
end Residual

/-!
## Main Result for straight-line programs
-/
attribute [grind =] id_eq

open MultiContext (plug)

/-! ### Invariant -/
section Invariant

/--
In the main proof, we will do induction on the context `C`, meaning that the
context considered in the inductive step will be a sub-context of the original
program context.

Within the proof, we will keep track of a residual variable set `Γ`, which has
all variables of the original program considered in previous steps of the
induction, thus we keep the following invariant about `Γ`.
-/
@[grind, grind cases] private structure InvariantAux
    (Γ : VarSet) (H : List (Hole n))
    (C : MultiContext ι n) (P : Pattern ι n) (ρ : SEnv ι) where
  /-- `C` is complete module `H` -/
  completeMod : C.CompleteMod H
  /-- `Γ` contains the results of `I[h]` iff `h ∈ H` -/
  results_subset_iff_mem : ∀ h, h ∈ H ↔ P[h].results ⊆ Γ
  /-- `Γ` contains the arguments of `I[h]` for each `h ∈ H` -/
  args_subset_of_mem : ∀ h ∈ H, P[h].args ⊆ Γ
  /-- `C.plug P` is well-formed with free variables `Γ`. -/
  wf : (C.plug P).WellFormed Γ
  /-- The pattern `P` does not redefine any of its own variables. -/
  nsP : P.NoShadowing
  /-- Each component of the pattern `P` is wellformed, for some other set of variables `Δ`. -/
  wfP : ∀ (k : Hole n), ∃ Δ, P[k].WellFormed Δ
  /-- The pattern `P` is well-behaved. -/
  wbP : P.WellBehaved
  /-- The equation invariant of `P[h]`, for any `h ∈ H`, is satisfied by `ρ`. -/
  eqnInv : ∀ h ∈ H, P[h].EqnInv ρ
  /-- `H` is closed under the precedence relation (≺). -/
  closed : ∀ l ∈ H, ∀ k, P.Prec k l → k ∈ H

private abbrev Invariant (C : MultiContext ι n) (P : Pattern ι n) (ρ : SEnv ι) : Prop :=
  ∃ Γ H, InvariantAux Γ H C P ρ

variable {Γ} {C : MultiContext ι n} {P : Pattern ι n} {ρ : SEnv ι} {i : Inst ι}

namespace InvariantAux

private theorem initial (wf : (C.plug P).WellFormed ∅) (hC : C.Complete) (hI : P.WellBehaved) :
    InvariantAux ∅ [] C P { } := by
  constructor
  case wfP =>
    show ∀ k : Hole n, ∃ Δ, P[k].WellFormed Δ
    sorry
  case nsP =>
    show P.NoShadowing
    apply MultiContext.noShadowing_of_plug_noShadowing
    · assumption
    · grind
  case results_subset_iff_mem =>
    simp
    sorry
  all_goals grind

private theorem of_cons_inst  :
    InvariantAux Γ H (.inl i :: C) P ρ
    → InvariantAux (i.resultsSet ∪ Γ) H C P (⟦i⟧ ρ) := by
  rintro ⟨_, _⟩
  have : ∀ x ∈ i.resultsSet, x ∉ P.results := by
    intro x hx hxI
    have : x ∉ (C.plug P).results := by grind
    obtain ⟨h, hhx⟩ : ∃ h : Hole n, x ∈ P[h].results := by
      exact Pattern.exists_hole_of_mem_results hxI
    have hhC : Sum.inr h ∈ C := by
      grind [MultiContext.CompleteMod]
    grind
  constructor
  case completeMod => simp_all
  case eqnInv =>
    intros;
    apply InstSeq.eqnInv_denote_inst_of_wellFormed (Γ := Γ)
    <;> grind
  case results_subset_iff_mem =>
    intros; sorry
  all_goals solve | assumption | grind

private theorem of_cons_hole :
    InvariantAux Γ H (.inr h :: C) P ρ →
    InvariantAux (P[h].results ∪ Γ) (h :: H)  C P (⟦P[h]⟧ ρ) := by
  intro inv
  constructor
  case completeMod => simpa using inv.completeMod
  case eqnInv =>
    sorry
  case results_subset_iff_mem =>
    intro k
    have := inv.results_subset_iff_mem
    simp only [List.mem_cons, Pattern.getElem_hole]
    suffices P[↑k].results ⊆ P[↑h].results ∪ Γ → k = h ∨ k ∈ H by
      constructor <;> grind
    by_cases P[k].results.Disjoint P[h].results
    case pos => grind
    case neg =>
      suffices k = h by grind
      sorry



    suffices P[↑h].args ⊆ Γ by
      simp only [List.mem_cons, Pattern.getElem_hole, forall_eq_or_imp]
      and_intros <;> (intros; and_intros <;> grind)
    grind -- by wellformedness of `C.plug I`


  case closed =>
    suffices ∀ (k : Hole n), P.Prec k h → k ∈ H by grind
    have subset := inv.subset_Γ_of_mem_H
    have closed := inv.closed;
    clear inv
    rintro k hk
    induction hk
    case prec k x l hres hargs =>
      sorry
    case trans => assumption


  case wfP => exact inv.wfP
  all_goals grind

  stop
  · simp_all
  · grind
  · grind
  · stop
    have hΔ : is.args ⊆ Γ := by grind
    replace his : is ⊆ I.collapse := by grind
    generalize Γ = Δ at ⊢ hΔ closed
    clear eqn
    intro x hx y hy
    induction is generalizing Δ with
    | nil => sorry
    | cons i is ih =>
        have his : is ⊆ I.collapse := by grind
        have hΔ' : is.args ⊆ i.resultsSet ∪ Δ := by grind
        specialize ih his _ hΔ'
        specialize ih <| by -- prove closedness
          clear ih
          intro x hx y hy
          by_cases x ∈ Δ; grind
          have : x ∈ i.resultsSet := by grind
          · rw [InstSeq.mem_usesAt'] at hy
            obtain ⟨j, hj, hxj, hy⟩ := hy
            obtain rfl : i = j := by
              have hi : i ∈ I.collapse := by grind
              have hj : j ∈ I.collapse := by grind
              apply InstSeq.eq_of_not_disjoint_results_of_noShadowing hi hj nsI
              grind
            rcases hy with ( (hy : y ∈ i.argsSet) | ⟨z, hzi, hyz⟩ )
            · have : y ∈ Δ := by grind
              grind
            · grind
        grind
  · stop
    intro x hx
    by_cases x ∈ Γ; grind
    have hx : x ∈ is.results := by grind
    · obtain ⟨Δ, wf⟩ : ∃ Δ, is.WellFormed Δ := by grind
      subst his
      rw [Pattern.eqnLemma_of_mem_results_get hx nsI]
      apply InstSeq.eqnLemma_denote_self _
      · grind
      · grind
  · grind

end InvariantAux

namespace Invariant

private theorem initial (wf : (C.plug P).WellFormed ∅) (hC : C.Complete) (wb : P.WellBehaved) :
    Invariant C P { } :=
  ⟨_, _, .initial wf hC wb⟩

private theorem of_invariant_cons_inst :
    Invariant (.inl i :: C) P ρ → Invariant C P (⟦i⟧ ρ) :=
  fun ⟨_, _, inv⟩ => ⟨_, _, inv.of_cons_inst⟩

private theorem of_invariant_cons_hole :
    Invariant (.inr h :: C) P ρ → Invariant C P (⟦P[h]⟧ ρ) :=
  fun ⟨_, _, inv⟩ => ⟨_, _, inv.of_cons_hole⟩

/--
If the invariant holds for a context that starts with hole `h`, then the
environment `ρ` satisfies the equation lemma for elements of `I` up-to that
particular hole `h`.

Recall that "up-to `h`" in particular does *not* include `h` itself.
-/
private theorem eqnInvUpTo_of_invariant_cons_hole :
    Invariant (.inr h :: C) P ρ → P.EqnInvUpTo h ρ := by
  rintro ⟨Γ, H, inv⟩ k hk
  suffices k ∈ H by apply inv.eqnInv _ this
  suffices k ∈ h :: H by
    have : k ≠ h := Hole.neq_of_prec (hp := by assumption) (wf := inv.wfP)
    grind
  apply (inv.of_cons_hole).closed h (by simp) _ hk

end Invariant
end Invariant

/--
Proving denotational refinement is sufficient for showing contextual refinement.
-/
theorem Pattern.ctxRefine_of_denoteRefine (S T : Pattern ι n)
    (hS : S.WellBehaved) (hT : T.WellBehaved)
    (h_denoteRefine : S.DenRefine T) :
    S.CtxRefine T := by
  intro C hC CS CT hCS hCT
  subst CS CT

  suffices ∀ ρ η, ρ ⊒ η →
      Invariant C S ρ →
      Invariant C T η →
      ⟦C.plug S⟧ ρ ⊒ ⟦C.plug T⟧ η by
    apply @this { } { } <;> solve
      | apply Invariant.initial <;> grind
      | grind
  clear hC hCS hCT

  induction C <;> (intro ρ η hρη hCS hCT)
  case nil => simpa
  case cons h_or_i C ih =>
    cases h_or_i with
    | inl i =>
        -- The LHS and RHS both start with the instruction `i` from the context.
        apply ih (⟦i⟧ ρ) (⟦i⟧ η)
        · grind
        · apply hCS.of_invariant_cons_inst
        · apply hCT.of_invariant_cons_inst
    | inr h =>
        -- The context starts with hole `h`, meaning that the LHS and RHS start
        -- with `S[h]` and `T[h]`, respectively
        simp only [MultiContext.plug_cons_hole, getElem_hole, InstSeq.denote_append]
        -- By the IH, and the preservation of the invariant, the following suffices:
        suffices ⟦S[h]⟧ ρ ⊒ ⟦T[h]⟧ η by
          apply ih (⟦S[h]⟧ ρ) (⟦T[h]⟧ η)
          · apply this
          · apply hCS.of_invariant_cons_hole
          · apply hCT.of_invariant_cons_hole
        -- Finally, the refinement follows from denotational refinement,
        -- using the fact that the invariant implies the equation invariant
        -- up-to the starting hole `h`.
        apply h_denoteRefine
        · assumption
        · apply hCS.eqnInvUpTo_of_invariant_cons_hole
        · apply hCT.eqnInvUpTo_of_invariant_cons_hole
