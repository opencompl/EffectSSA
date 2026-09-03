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
  /-- `Γ` contains the arguments of `I[h]` for each `h ∈ H` -/
  args_subset_of_mem : ∀ h ∈ H, P[h].args ⊆ Γ
  /-- `Γ` contains the results of `I[h]` for each `h ∈ H`. -/
  results_subset_of_mem : ∀ h ∈ H, P[h].results ⊆ Γ
  /--
  If any of the results of a pattern component `P[k]` are present in `Γ`,
  this variable must have come from `P[k]`, and thus `k ∈ H`.
  -/
  results_covered : ∀ (k : Hole n) (x : VarId),
    x ∈ P[k].results → x ∈ Γ → k ∈ H
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

/--
If `P[h].args ⊆ Γ`, all "results-covered" holes are in `H`, and `H` is closed
under precedence, then any hole `k` that precedes `h` must be in `H`.
-/
private theorem closed_of_prec
    {Γ : VarSet} {H : List (Hole n)} {P : Pattern ι n} {h : Hole n}
    (hargs_h : ∀ x ∈ P[h].args, x ∈ Γ)
    (hcovered : ∀ (k : Hole n) (x : VarId), x ∈ P[k].results → x ∈ Γ → k ∈ H)
    (hclosed : ∀ l ∈ H, ∀ k, P.Prec k l → k ∈ H)
    {k : Hole n} (hkl : P.Prec k h) :
    k ∈ H := by
  suffices ∀ (k' l' : Hole n), P.Prec k' l' → l' ∈ h :: H → k' ∈ H by
    grind
  intro k' l' hkl'
  induction hkl' with
  | @prec k _ l  =>
      rw [List.mem_cons]
      rintro (rfl | hl)
      · grind
      · apply hclosed _ hl _ <| Pattern.Prec.prec ..
        <;> assumption
  | trans => grind

open MultiContext in
private theorem initial (wf : (C.plug P).WellFormed ∅) (hC : C.Complete) (hI : P.WellBehaved) :
    InvariantAux ∅ [] C P { } := by
  constructor
  case nsP => exact noShadowing_of_plug_noShadowing hC wf.noShadowing
  case wfP => intro k; apply wellFormed_getElem_of_plug_wellFormed wf (hC k List.not_mem_nil)
  all_goals solve | assumption | grind

private theorem of_cons_inst  :
    InvariantAux Γ H (Sum.inl i :: C) P ρ
    → InvariantAux (i.resultsSet ∪ Γ) H C P (⟦i⟧ ρ) := by
  intro inv
  obtain ⟨hi_args, hi_disj, hwf_C⟩ := by
    simpa only [MultiContext.plug_cons_inst, InstSeq.wellFormed_cons]
      using inv.wf
  have hi_wf : i.WellFormed Γ := ⟨hi_args, hi_disj⟩
  have { .. } := inv
  constructor
  case completeMod =>
    intro k hk
    have hmem := inv.completeMod k hk
    simp only [List.mem_cons] at hmem
    rcases hmem with heq | hin
    · cases heq
    · exact hin
  case results_covered =>
    -- No result of `i` can also be a result of the pattern `P`.
    have h_disj_P : ∀ x ∈ i.resultsSet, x ∉ P.results := by
      intro x hx hxP
      obtain ⟨k, hxk⟩ := Pattern.exists_hole_of_mem_results hxP
      by_cases hkH : k ∈ H
      · grind
      · have hkC : Sum.inr k ∈ C := by simpa using inv.completeMod k hkH
        have hxC : x ∈ (C.plug P).results := by grind
        grind
    intro k x hxk hx
    suffices x ∈ Γ by
      exact inv.results_covered k x hxk this
    suffices x ∉ i.resultsSet by grind
    intro hc
    suffices x ∈ P.results by grind
    suffices P[k] ∈ P by grind
    grind

  case eqnInv =>
    intro h hh
    have hwb_h : P[h].WellBehaved := inv.wbP _ (by grind)
    apply InstSeq.eqnInv_denote_inst_of_wellFormed
    <;> solve | assumption | grind
  all_goals solve | assumption | grind

private theorem of_cons_hole :
    InvariantAux Γ H (Sum.inr h :: C) P ρ
    → InvariantAux (P[h].results ∪ Γ) (h :: H) C P (⟦P[h]⟧ ρ) := by
  intro inv
  obtain ⟨hwf_h, hwf_C⟩ := by
    simpa only [MultiContext.plug_cons_hole, InstSeq.wellFormed_append] using inv.wf
  have hwb_h : P[h].WellBehaved := inv.wbP _ (by grind)
  have { .. } := inv
  constructor
  case completeMod => intro k hk; grind [inv.completeMod k]
  case results_covered =>
    intro k x hxk hx
    rcases VarSet.mem_union.mp hx with hxh | hxΓ
    · -- `x ∈ P[h].results` and `x ∈ P[k].results`. Show `k = h ∨ k ∈ H`.
      by_cases hkh : k = h
      · grind
      · suffices k ∈ H by grind
        false_or_by_contra
        have hkC : Sum.inr k ∈ C := by grind [inv.completeMod k]
        have hxC : x ∈ (C.plug P).results := by grind
        grind
    · grind
  case eqnInv =>
    intro k hk
    simp only [List.mem_cons] at hk
    rcases hk with rfl | hkH
    · exact InstSeq.eqnInv_denote_self hwb_h hwf_h
    · have hwb_k : P[k].WellBehaved := by grind
      apply InstSeq.eqnInv_denote_other hwb_k hwf_h
      <;> grind
  case closed =>
    intro l hl k hkl
    simp only [List.mem_cons] at hl
    rcases hl with rfl | hlH
    · suffices k ∈ H by grind
      apply closed_of_prec
      · intro x; apply VarSet.mem_of_subset_of_mem hwf_h.args
      all_goals grind
    · grind
  all_goals solve | assumption | grind

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
