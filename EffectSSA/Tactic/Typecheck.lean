import EffectSSA.Types


/-!
# Typechecking Tactic

This files defines a `typecheck` tactic, which automatically infers well-typedness
of programs.
-/

/-
TODO: I should port `typecheck` to use the new `cbv` tactic that exists in recent
nigtlies, once I've actually updated to a recent-enough nightly.

I should be able to reuse the decidability instance for something
to actually reduce.
-/

namespace EffectSSA.Tactic

macro "typecheck" : tactic => `(tactic|(
  simp -failIfUnchanged only [
    typecheck,
    InstructionSeq.WellTypedWith, Program.WellTyped,
    Context.isUnrestricted_empty,
    List.length_nil,
    ↓existsAndEq, and_true, true_and,
  ]
  grind
))
