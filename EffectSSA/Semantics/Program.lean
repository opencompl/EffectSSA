import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Syntax
import EffectSSA.Trace
import EffectSSA.Semantics.Basic
import EffectSSA.Semantics.Merge
import EffectSSA.Semantics.Environment
import EffectSSA.Semantics.ExecM

/-!
# Whole-Program Semantics

This file composes the semantic functions for each instruction into a semantics
for whole programs.
-/
namespace EffectSSA
open Semantics
variable {τ : Ty} [MemoryModel τ]

/-!
## Instruction Semantics
--------------------------------------------------------------------------------
-/

/-
TODO: in execM I probably want to change it so that I erase variables FIRST,
and then snoc more things into the environment. Cross-reference the typing rules,
and in particular, the TInstruction.exec proving effort, which is currently
blocked in what seems like an unprovable state
-/

/--
Execute a single instruction `i` in a specific environment, returning a new
environment with the results of `i` added to it, and any linear values consumed
by `i` removed.
-/
def Instruction.execM (env : Environment τ) : (i : Instruction τ) → ExecM τ (Environment τ)
  -- Implicit (i.e, side-effecting) memory operations
  | .loadI t p => do
    let val ← modifyGetTrace <| load t (←env.getPtr p)
    return env.snoc val
  | .storeI t p x => do
    modifyTrace <| store (←env.getPtr p) (←env.getData x t)
    return env
  | .allocI t p => do
    modifyTrace (alloc t (←env.getPtr p))
    return env
  | .freeI t p => do
    modifyTrace (free t (←env.getPtr p))
    return env
  -- EffectSSA memory operations
  | .loadE t eff p => do
    let (val, trace) := load t (←env.getPtr p) (←env.getEff eff)
    return (env.snoc trace |>.snoc val).eraseVar eff
  | .storeE t eff p x => do
    let trace := store (←env.getPtr p) (←env.getData x t) (←env.getEff eff)
    return (env.snoc trace).eraseVar eff
  | .allocE t eff p => do
    let trace := alloc t (←env.getPtr p) (←env.getEff eff)
    return (env.snoc trace).eraseVar eff
  | .freeE t eff p => do
    let trace := free t (←env.getPtr p) (←env.getEff eff)
    return (env.snoc trace).eraseVar eff
  -- Split / Merge
  | .split eff => do
    let trace := Semantics.split (← env.getEff eff)
    return (env.snoc trace |>.snoc trace).eraseVar eff
  | .merge eff₁ eff₂ => do
    let trace := Semantics.merge (← env.getEff eff₁) (← env.getEff eff₂)
    return (env.snoc trace).eraseVar eff₁ |>.eraseVar eff₂
  -- Effect state bookkeeping operations
  | .createEff => do
    let trace ← takeTrace
    return env.snoc trace
  | .consumeEff e => do
    putTrace (←env.getEff e)
    return env.eraseVar e
where
  /--
  Modify the current trace in the state and return a value computed from the original trace.
  If the state is absent, execute `f` as if the state was UB, and
    store the resulting state.
  -/
  modifyGetTrace {α} (f : Trace τ → α × Trace τ) : ExecM τ α :=
    modifyGet fun (es? : Option _) =>
      let ⟨x, es⟩ := f (es?.getD .ub)
      (x, some es)
  /--
  Modify the current trace in the state.
  If the state is absent, act as if the state was UB.
  -/
  modifyTrace (f : Trace τ → Trace τ) : ExecM τ Unit :=
    modifyGetTrace (fun es => ((), f es))
  /--
  Take the current trace from the state, such that it is absent after.
  Otherwise, if the trace is already absent, modify the state to be UB,
  and return a UB trace
  -/
  takeTrace : ExecM τ (Trace τ) :=
    modifyGet fun
      | none => (.ub, some .ub)
      | some es => (es, none)
  /--
  Set the current trace in the state, assuming it was absent.
  Otherwise, if a trace is already present, replace it with UB.
  -/
  putTrace (es : Trace τ) : ExecM τ Unit :=
    modify fun
      | none => some es
      | some _ => some .ub

@[inherit_doc Instruction.execM]
def Instruction.exec (env : Environment τ) (i : Instruction τ) (es : Option (Trace τ)) :
    Option (Environment τ × Option (Trace τ)) :=
  (i.execM env).run es

/-!
## Sequence & Program Semantics
--------------------------------------------------------------------------------
-/

/--
Return the environment after executing all instructions in sequence `p`,
starting from environment `env`.
-/
def InstructionSeq.execM (env : Environment τ) (p : InstructionSeq τ) : ExecM τ (Environment τ) :=
  p.foldlM Instruction.execM env

@[inherit_doc InstructionSeq.execM]
def InstructionSeq.exec (env : Environment τ) (is : InstructionSeq τ) (es : Option (Trace τ)) :
    Option (Environment τ × Option (Trace τ)) :=
  (is.execM env).run es

/--
Return the value assigned to the return variables of a program (fragment) `p`,
after executing the instruction sequence of `p` starting from environment `env`.

Executes against the trace in the mondic state.
-/
def Program.execM (env : Environment τ) (p : Program τ) : ExecM τ (Environment τ) := do
  let env ← p.instructions.execM env
  let res : ExecM.TypeErrM _ := env.limitTo? p.returnVars
  res

/--
Return the value assigned to the return variables of a program (fragment) `p`,
after executing the instruction sequence of `p` starting from environment `env`.

Executes against an explicitly passed trace, returning the resulting trace.
-/
def Program.exec (env : Environment τ) (p : Program τ) (es : Option (Trace τ)) :
    Option (Environment τ × Option (Trace τ)) := do
  (p.execM env).run es

/--
Execute a complete *closed* program `p`, yielding the computed return values and
the final trace of all events that happened during execution.

This differs from `exec` in that execution starts with an empty environment and
empty initial trace, since we assume `p` represents a complete computation.

Returns `none` if execution threw a type-error, which is impossible when the
program is well-typed (see `isSome_execClosed?`).
-/
def Program.execClosed (p : Program τ) : Option (Environment τ × Option (Trace τ)) := do
  p.exec ∅ (some ∅)
