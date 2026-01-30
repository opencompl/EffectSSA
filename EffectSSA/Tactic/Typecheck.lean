import EffectSSA.Types


/-!
# Typechecking Tactic

This files defines a `typecheck` tactic, which automatically infers well-typedness
of programs.

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
