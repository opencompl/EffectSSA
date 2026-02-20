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
A program context is, intuitively, a program with a "hole" in it, that may be
filled by substituting in another program.

At the same time, we want the context to be able to contain intermediate
let-bindings, without affecting the "shape" of the hole. Thus, a context is
implemented in terms of two programs, `pre` and `post`, such that the "hole"
is implicitly between the two programs, where:
- `pre` should be welltyped under the empty context
- The return types of `pre` indicate the free variables available to the "hole"
- The free variables of `post` indicate the expected return types of the "hole"
-/
structure ProgramContext τ : Type where
  pre  : Program τ
  post : Program τ

/-!
## API
--------------------------------------------------------------------------------
-/
namespace ProgramContext
variable {τ} [MemoryModel τ] {Δ : Context τ}

/--
Execute a program under the given context.

That is, plug program `p` into the hole of context `C`, and evaluate the
resulting program.
-/
def execProgram (C : ProgramContext τ) (p : Program τ) :
    Option (Environment τ) := do
  let (env, es) ← C.pre.execClosed
  let (env, es) ← p.exec (.ofList env) es
  let (env, _) ← C.post.exec (.ofList env) es
  return .ofList env
