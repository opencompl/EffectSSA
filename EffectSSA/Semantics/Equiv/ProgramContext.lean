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
An `n`-ary program context is, intuitively, a program with a `n` "holes" in it,
that may be filled by substituting in another program.

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
  ctx : List (Program τ)

structure HoleSpec τ where
  /-- The context in which to type the hole. -/
  Γ : Context τ
  /-- Return variables to be passed to the next hole. -/
  retInteral : List τ.Typ
  /-- Return variables to be passed to the context -/
  retExternal : List τ.Typ

/--
A typed program context `TProgramContext Γ ts` bundles proofs that the "hole"
of the context is shapped exactly like a `TProgram Γ ts`.
-/
inductive ProgramContext.WellFormed : Context τ → ProgramContext τ → (η : List (HoleSpec τ)) → Type where
  /-- A context without any holes is just a program. -/
  | nil {P : Program τ} : P.WellTyped Γ [t] → WellFormed Γ ⟨[P]⟩ []
  /--  -/
  | cons {P : Program τ} : WellFormed Γ ⟨P :: C⟩ (σ :: η)


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
