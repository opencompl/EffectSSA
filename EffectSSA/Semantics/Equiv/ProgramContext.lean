import EffectSSA.Semantics.Environment
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas
import EffectSSA.Semantics.Typed
import EffectSSA.Types
import EffectSSA.Syntax.Typed

import EffectSSA.Tactic.Typecheck

/-!
# Closing Environment

This file defines *closing* environments, via which we'll define contextual
equivalence.
-/
namespace EffectSSA.Semantics

noncomputable section -- TODO: #19 remove once ITC has been implemented

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

Note: although this is not enforced in `ProgramContext`, the `post` program is
expected to have exactly one return variable. Since we universally quantiy
over context when defining contextual equivalence, we don't lose any expressive
power by disallowing multiple return variables, but it does make things easier.
-/
structure ProgramContext τ : Type where
  pre  : Program τ
  post : Program τ

/--
A typed program context `TProgramContext Γ ts` bundles proofs that the "hole"
of the context is shapped exactly like a `TProgram Γ ts`.
-/
structure TProgramContext (Γ : Context τ) (ts : List τ.Typ) where
  ctx : ProgramContext τ
  /--
  The return type of the context (when filled).

  Recall that we expect a program context to return only a single variable at the
  end. Furthermore, an explicit goal of using contextual equivalence is to be able
  to equate traces where events have been moved around in irrelvevant ways,
  without having to explicitly define when that is the case. That is why we don't
  want the precise structure of the trace to leak out of the context and thus we
  mandate that the return type *must* be a plain data type.
  -/
  finalType : τ.DType
  wt_pre : ctx.pre.WellTyped ∅ Γ.toList
  wt_post : ctx.post.WellTyped ⟨ts⟩ [finalType]


/-! ### Grind Attributes -/
grind_pattern TProgramContext.wt_pre => (TProgramContext.ctx self).pre
grind_pattern TProgramContext.wt_post => (TProgramContext.ctx self).post

/-!
## API
--------------------------------------------------------------------------------
-/
variable {τ} {Γ Δ : Context τ}

def TProgramContext.pre (C : TProgramContext Γ ts) : TProgram ∅ Γ.toList where
  program := C.ctx.pre
def TProgramContext.post (C : TProgramContext Γ ts) : TProgram ⟨ts⟩ [C.finalType] where
  program := C.ctx.post

/--
Execute a program under the given context.
That is, plug program `p` into the hole of context `C`, and evaluate the
resulting program, returning `none` when the program is malformed, or has more
than a single return variable.
-/
def ProgramContext.execProgram [LawfulMemoryModel τ] (C : ProgramContext τ) (p : Program τ) :
    Option τ.Val := do
  let (env, es) ← C.pre.execClosed
  let (env, es) ← p.exec env es
  let (env, _) ← C.post.exec env es
  if env.size = 1 then
    env.get? ⟨0⟩
  else
    none

/--
Execute a (typed) program under the given (typed) context.

That is, plug program `p` into the hole of context `C`, and evaluate the
resulting program.
-/
def TProgramContext.execProgram [LawfulMemoryModel τ] (C : TProgramContext Γ ts) (p : TProgram Γ ts) :
    τ.TVal C.finalType :=
  let (env, es) := C.pre.execClosed
  let (env, es) := p.exec env es
  let (env, _) := C.post.exec env es
  env.get ⟨⟨0⟩, rfl⟩

/-!
## Lemmas
--------------------------------------------------------------------------------
-/
variable {ts} (C : TProgramContext Γ ts)

@[simp, grind =] theorem TProgramContext.ctx_pre : C.ctx.pre = C.pre.program := by rfl
@[simp, grind =] theorem TProgramContext.ctx_post : C.ctx.post = C.post.program := by rfl

@[simp, grind =] theorem TProgramContext.ctx_exec_eq [LawfulMemoryModel τ] (p : TProgram Γ ts) :
    C.ctx.execProgram p.program = some (C.execProgram p).toVal := by
  simp [execProgram, ProgramContext.execProgram]
