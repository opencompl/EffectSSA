module

public import EffectSSA.ProofSketch.InstSeq
public import EffectSSA.ProofSketch.Pattern
public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.EqnInv

/-!
# Precedence Relation

This file defines the precedence relation on holes, written as `≺` in the paper.
-/
public section
namespace EffectSSA.ProofSketch
variable [SSA ι σ ν]

/-! ## Definition -/

/--
With respect to a pattern `P`, hole `k` (strictly) precedes hole `l` when
`P[k]` defines a variable (transitively) used as argument to `P[l]`.
-/
inductive Pattern.Prec (P : Pattern ι n) : Hole n → Hole n → Prop
  | prec : x ∈ P[k].results → x ∈ P[l].args → P.Prec k l
  | trans : P.Prec k l → P.Prec l m → P.Prec k m

/--
`P.PrecEq k l` holds iff `k = l` or `P.Prec k l`.

That is, `PrecEq` is the reflexive closure of `Prec`.
-/
abbrev Pattern.PrecEq (rw : Pattern ι n) (k l : Hole n) :=
  k = l ∨ rw.Prec k l

/--
`P.EqnInvUpTo l` holds for some environment `ρ` when that environment satisfies
the equation invariant of `P[k]` for any hole `k` that
(strictly) precedes the given hole `l` (wrt the given rewrite).
-/
@[expose] def Pattern.EqnInvUpTo (P : Pattern ι n) (l : Hole n) (ρ : SEnv ι) : Prop :=
  ∀ k, P.Prec k l → (P[k]).EqnInv ρ


/-! ## Main Characterization -/
section Characterize
variable {C : MultiContext ι n} {P : Pattern ι n} {Γ : VarSet} {H : List (Hole n)}

theorem Pattern.prec_iff
    (h_wf : (C.plug P).WellFormed ∅)
    (h_cmod : C.Complete)
    {k l} (h_prec : P.Prec k l) :
    ∀ lLoc : Nat, C[lLoc]? = some (.inr l) →
      ∃ kLoc, C[kLoc]? = some (.inr k) ∧ kLoc < lLoc := by
  -- **AI DISCLOSURE**: LLM-generated proof
  induction h_prec with
  | prec hxk hxl =>
    rename_i src var tgt
    intro lLoc hl
    -- `.inr src ∈ C`; we must find a position of src before lLoc.
    have hsrcInC : (Sum.inr src : Inst ι ⊕ Hole n) ∈ C := h_cmod _ (by simp)
    have hlLt : lLoc < C.length := (List.getElem?_eq_some_iff.mp hl).1
    have hlEq : C[lLoc]'hlLt = .inr tgt := (List.getElem?_eq_some_iff.mp hl).2
    let A : MultiContext ι n := C.take lLoc
    let B : MultiContext ι n := C.drop (lLoc + 1)
    have hDrop : C.drop lLoc = .inr tgt :: B := by
      show _ = _
      rw [List.drop_eq_getElem_cons hlLt, hlEq]
    have hCsplit : C = A ++ .inr tgt :: B := by
      show C = _
      rw [← hDrop, List.take_append_drop]
    have hSplit : C.plug P = A.plug P ++ P[tgt] ++ B.plug P := by
      rw [hCsplit]; simp
    have h_wf' := hSplit ▸ h_wf
    obtain ⟨h_apl, h_b⟩ := InstSeq.wellFormed_append.mp h_wf'
    obtain ⟨h_a, h_pl⟩ := InstSeq.wellFormed_append.mp h_apl
    -- var ∈ P[tgt].args ⊆ (A.plug P).results ∪ ∅
    have hVarA : var ∈ (A.plug P).results := by
      have := VarSet.mem_of_subset_of_mem h_pl.args hxl
      grind
    -- We claim `.inr src ∈ A`: if it lived in
    -- `.inr tgt :: B`, then `var` would also appear in `(P[tgt] ++ B.plug P).results`,
    -- contradicting the well-formedness (via NoShadowing) of `C.plug P`.
    have hDisj : (A.plug P).results.Disjoint (P[tgt] ++ B.plug P).results := by
      have hDisj_pl : P[tgt].results.Disjoint (A.plug P).results := by
        have := h_pl.results; grind
      have hDisj_b : (B.plug P).results.Disjoint (A.plug P).results := by
        have := h_b.results
        grind
      rw [InstSeq.results_append]
      grind
    have hsrcInA : (Sum.inr src : Inst ι ⊕ Hole n) ∈ A := by
      rw [hCsplit, List.mem_append] at hsrcInC
      rcases hsrcInC with hInA | hInTail
      · exact hInA
      exfalso
      have hVarRHS : var ∈ (P[tgt] ++ B.plug P).results := by
        rw [InstSeq.results_append]
        rw [List.mem_cons] at hInTail
        grind
      grind
    -- Now translate a position of `.inr src` in A into a position in C.
    obtain ⟨aLoc, haLt, haEq⟩ := List.getElem_of_mem hsrcInA
    have haLtLoc : aLoc < lLoc := by grind
    refine ⟨aLoc, ?_, haLtLoc⟩
    show C[aLoc]? = some (Sum.inr src)
    grind
  | trans => grind

/--
Precedence is irreflexive whenever `P` admits a well-formed plug (modulo `H`)
whose free variables are covered by `H`, and `H` is closed under precedence.
Specialised from `prec_iff` at `k = l`, where the position argument collapses.
-/
@[grind →] theorem Hole.neq_of_prec
    (h_wf : (C.plug P).WellFormed ∅)
    (h_cmod : C.Complete)
    {k l} (h_prec : P.Prec k l) : k ≠ l := by
  -- **AI DISCLOSURE**: LLM-generated proof
  rintro rfl
  suffices h : ∀ kLoc, C[kLoc]? ≠ some (Sum.inr k) by
    obtain ⟨kLoc, hkLt, hkEq⟩ := List.getElem_of_mem (h_cmod k (by simp))
    exact h kLoc (List.getElem?_eq_some_iff.mpr ⟨hkLt, hkEq⟩)
  intro kLoc
  induction kLoc using Nat.strongRecOn with | ind kLoc ih =>
    grind [Pattern.prec_iff]

end Characterize
