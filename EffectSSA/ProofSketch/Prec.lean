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

/-! ## Basic Lemmas -/
section Lemmas

end Lemmas


/-! ## Main Characterization -/

/--
If `C[P]` is well-formed, and if hole `k` precedes hole `l` (wrt `P`),
then that `k` must occur before `l` in the context `C`.
-/
theorem Pattern.prec_iff {C : MultiContext ι n} {P : Pattern ι n}
    (h_wf : (C.plug P).WellFormed ∅)
    {k l} (h_prec : P.Prec k l) :
    ∀ kLoc lLoc : Nat,
      C[kLoc]? = some (.inr k)
      → C[lLoc]? = some (.inr l)
      → kLoc < lLoc := by
  intro kLoc lLoc hk hl
  sorry
