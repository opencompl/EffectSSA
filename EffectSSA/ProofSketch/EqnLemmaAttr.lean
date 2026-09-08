module

public import Lean.Meta.Tactic.Simp
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# `eqn_lemma` simp attribute

Registers the simp set that powers the `reduceEqnLemmaUpTo` tactic (defined
in `EffectSSA.ProofSketch.Tactic`).  It bundles the general-purpose unfolding
lemmas / simprocs from that file together with any case-study-specific
rewrites (concrete `Rewrite` definitions, per-instruction `argsSet_*` /
`resultsSet_*` / `denote_*` lemmas) tagged in downstream files.

The registration lives in its own file because a Lean simp attribute cannot
be added to declarations in the same file where it was registered.
-/

/-- Simp set for `reduceEqnLemmaUpTo`; see the module docstring. -/
register_simp_attr eqn_lemma
