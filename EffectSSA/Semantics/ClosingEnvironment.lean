import EffectSSA.Semantics.Environment
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas
import EffectSSA.Types

import EffectSSA.Tactic.Typecheck

/-!
# Closing Environment

This file defines *closing* environments, via which we'll define contextual
equivalence.
-/
namespace EffectSSA.Semantics
variable {τ} [MemoryModel τ]

/-!
## ClosingEnvironment Definition
--------------------------------------------------------------------------------
-/

/--
A closing (semantic) context for a (typing) context `Δ` is some program `p`
which is well-typed under the empty context, with `Δ` as its return types.

A closing environment for a specific context `Δ` is an environment which can
be produced by some well-typed program, whose return types correspond to `Δ`,
together with the trace of event
-/
structure ClosingContext (Δ : Context τ) : Type where
  program : Program τ
  env : Environment τ
  trace : Trace τ
  wellTyped : Program.WellTyped ∅ program Δ.toList
  exec_program :
    program.execClosed = some (env.toList, trace)

/-!
## API
--------------------------------------------------------------------------------
-/
namespace ClosingEnvironment
variable {Δ : Context τ} [MemoryModel τ]

def ofProgram (program : Program τ) (wt : Program.WellTyped ∅ program Δ.toList := by typecheck)
    : ClosingContext Δ :=
  have exec : program.execClosed.isSome := Program.isSome_execClosed_of_wellTyped wt
  {
    program := program
    env := .ofList (program.execClosed.get exec).1
    trace := (program.execClosed.get exec).2
    wellTyped := wt
    exec_program := by simp
  }
