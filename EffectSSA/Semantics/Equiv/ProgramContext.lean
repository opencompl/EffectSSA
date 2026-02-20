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
structure ProgramContext τ : Type where
  program : Program τ

/-!
FIXME: the context as phrased above is not quite enough, as it only captures
a program that has a hole at the very end. However, equivalence under this context
does *not* say anything about the produced traces after execution.

Thus, the context should be generalized to also have a "suffix" program.

-/

/-!
## API
--------------------------------------------------------------------------------
-/
namespace ProgramContext
variable {τ} [MemoryModel τ] {Δ : Context τ}

/--
Execute a program under the given context.
-/
def execProgram (C : ProgramContext τ) (p : Program τ) :
    Option (Environment τ) := do
  let (env, es) ← C.program.execClosed
  let (env, _) ← p.exec (.ofList env) es
  return .ofList env
