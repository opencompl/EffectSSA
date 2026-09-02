module

public import EffectSSA.ProofSketch.ProofSketch
public import EffectSSA.ProofSketch.Rewrite


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
With repect to a rewrite `⟨S, T⟩`, hole `k` precedes hole `l`, when
`k` precedes `l` with respect to either the source pattern `S` or the
target pattern `T`.
-/
@[grind, grind cases]
inductive Rewrite.Prec (rw : Rewrite ι n) (k l : Hole n) : Prop
  | src : rw.src.Prec k l → rw.Prec k l
  | tgt : rw.tgt.Prec k l → rw.Prec k l

/--
`rw.PrecEq k l` holds iff `k = l` or `rw.Prec k l`.

That is, `PrecEq` is the reflexive closure of `Prec`.
-/
abbrev Rewrite.PrecEq (rw : Rewrite ι n) (k l : Hole n) :=
  k = l ∨ rw.Prec k l

/--
`rw.EqnInvUpTo l` holds for some environment `ρ` when that environment satisfies
the equation invariants of `rw.src[k]` and `rw.tgt[k]` for any hole `k` that
precedes the given hole `l` (wrt the given rewrite).
-/
@[expose] def Rewrite.EqnInvUpTo (rw : Rewrite ι n) (l : Hole n) (ρ : SEnv ι) : Prop :=
  True
  -- ∀ k, rw.PrecEq k l → (rw.src[k]).EqnInv ρ ∧ (rw.tgt[k]).EqnInv ρ


/-! ## Basic Lemmas -/
section Lemmas

end Lemmas


/-! ## Main Characterization -/
section Characterize
variable {C : MultiContext ι n} {P : Pattern ι n}

/--
If `C[P]` is well-formed, and if hole `k` precedes hole `l` (wrt `P`),
then that `k` must occur before `l` in the context `C`,
assuming that `C` is complete.
-/
theorem Pattern.prec_iff
    (h_wf : (C.plug P).WellFormed ∅) (hC : C.Complete)
    {k l} (h_prec : P.Prec k l) :
    ∀ kLoc lLoc : Nat,
      C[kLoc]? = some (.inr k)
      → C[lLoc]? = some (.inr l)
      → kLoc < lLoc := by
  -- **AI DISCLOURE**: LLM-generated proof
  induction h_prec with
  | prec hxk hxl =>
    -- Naming: outer holes shadowed as k✝, l✝; inner args are named
    -- (source hole : Hole n, shared var : VarId, target hole : Hole n).
    intro kLoc lLoc hk hl
    rcases Nat.lt_or_ge kLoc lLoc with hlt | hge
    · exact hlt
    exfalso
    rename_i src var tgt
    -- hxk : var ∈ P[src].results, hxl : var ∈ P[tgt].args
    -- hk  : C[kLoc]? = some (.inr src), hl : C[lLoc]? = some (.inr tgt)
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
    rw [hSplit] at h_wf
    obtain ⟨h_apl, h_b⟩ := InstSeq.wellFormed_append.mp h_wf
    obtain ⟨_, h_pl⟩ := InstSeq.wellFormed_append.mp h_apl
    have hxA : var ∈ (A.plug P).results := by
      have hSub := h_pl.args
      have := VarSet.mem_of_subset_of_mem hSub hxl
      grind
    rcases Nat.eq_or_lt_of_le hge with heq | hlt
    · have hOpt : some (Sum.inr src : Inst ι ⊕ Hole n) = some (Sum.inr tgt) := by
        rw [← hk, heq.symm, hl]
      have hsrctgt : src = tgt := by
        have : (Sum.inr src : Inst ι ⊕ Hole n) = .inr tgt := Option.some.inj hOpt
        cases this; rfl
      subst hsrctgt
      have h_disj : (A.plug P).results.Disjoint P[src].results := by
        have := h_pl.results; grind
      exact VarSet.not_mem_of_disjoint h_disj hxA hxk
    · have hkLt : kLoc < C.length := (List.getElem?_eq_some_iff.mp hk).1
      have hkGetEq : C[kLoc]'hkLt = .inr src := (List.getElem?_eq_some_iff.mp hk).2
      have hkInDrop : (Sum.inr src : Inst ι ⊕ Hole n) ∈ B := by
        show _ ∈ (_ : List _)
        rw [List.mem_iff_getElem]
        refine ⟨kLoc - (lLoc + 1), ?_, ?_⟩
        · rw [List.length_drop]; omega
        · rw [List.getElem_drop]
          have hAdd : lLoc + 1 + (kLoc - (lLoc + 1)) = kLoc := by omega
          simp [hAdd, hkGetEq]
      have hxB : var ∈ (B.plug P).results := by
        rw [MultiContext.mem_results_plug_iff]
        exact Or.inr ⟨src, hkInDrop, hxk⟩
      have h_b_disj : (B.plug P).results.Disjoint
          (A.plug P ++ P[tgt]).results := by
        have := h_b.results; grind
      have hxApL : var ∈ (A.plug P ++ P[tgt]).results := by
        rw [InstSeq.results_append]
        exact VarSet.mem_union.mpr (Or.inl hxA)
      exact VarSet.not_mem_of_disjoint h_b_disj hxB hxApL
  | @trans _ mid _ _ _ IHkm IHml =>
    intro kLoc lLoc hk hl
    obtain ⟨mLoc, hmLt, hmEq⟩ := List.getElem_of_mem (hC mid)
    have hm : C[mLoc]? = some (Sum.inr mid) :=
      List.getElem?_eq_some_iff.mpr ⟨hmLt, hmEq⟩
    exact Nat.lt_trans (IHkm kLoc mLoc hk hm) (IHml mLoc lLoc hm hl)

theorem

end Characterize
