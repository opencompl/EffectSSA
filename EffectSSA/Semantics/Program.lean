import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Syntax
import EffectSSA.Trace
import EffectSSA.Semantics.Basic
import EffectSSA.Semantics.Merge
import EffectSSA.Semantics.Environment

/-!
# Whole-Program Semantics

This file composes the semantic functions for each instruction into a semantics
for whole programs.
-/
namespace EffectSSA
open Semantics
variable (τ : Ty) [MemoryModel τ]

/-! First, we define the monad with program execution side-effects. -/
section ExecM

/-- `ExecM` is the monad in which programs are executed. -/
def ExecM := StateT (Trace τ) TypeErrM
  where
    /-- `TypeErrM α` represents either a type-error, or a value of type `α`. -/
    TypeErrM := Option

/-! Show that `ExecM` is in fact a (lawful) monad. -/
section Monad
instance : Monad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : LawfulMonad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadState (Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadStateOf (Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
end Monad

end ExecM

-- From here on, `τ` will be implicit
variable {τ}

/--
`env.getAs v t` retrieves the value environment `env` associates with a
variable `v`, and then attempts to coerce this to be a typed value of type `t`.
Throws a type error if `v` has a type different from `t`.

See also `Environment.getAs?`, which returns none instead.
-/
def Semantics.Environment.getAs (env : Environment τ n) (v : Var n) (t : τ.Typ) : ExecM τ (τ.TVal t) :=
  -- Lifts `getAs?` into the `ExecM` monad, treating `none` as a type error
  fun es => (env.getAs? v t).map (·, es)

/--
Create a new environment by prepending a value to the front of an environment.
-/
def Semantics.Environment.cons (v : τ.Val) (env : Environment τ n) : Environment τ (n + 1) :=
  -- Prepends `v` to the environment, making it the new variable 0
  sorry

/--
Create a new environment by removing the variable at position `v` from the environment.
The result type matches `Instruction.results` for `consumeEff`.
-/
def Semantics.Environment.remove (env : Environment τ n) (v : Var n) : Environment τ ((n : Int) + -1).toNat :=
  -- Removes the variable at position `v`, shifting all subsequent variables down
  sorry

/--
Execute a single instruction `i` in a specific environment, returning a new
environment with the results of `i` added to it, and any linear values consumed
by `i` removed.
-/
def Instruction.exec (env : Environment τ n) : (i : Instruction τ n) → ExecM τ (Environment τ i.results)
  | .loadI t p => do
    let .ptr ptr_val ← env.getAs p .ptr
    let val ← modifyGetTrace (load t ptr_val)
    return env.cons ⟨_, .data val⟩
  | .storeI t p x => do
    let .ptr ptr_val ← env.getAs p .ptr
    let .data x_val ← env.getAs x (.data t)
    modifyTrace (store ptr_val x_val)
    return env
  | .allocI t p => do
    let .ptr ptr_val ← env.getAs p .ptr
    modifyTrace (alloc t ptr_val)
    return env
  | .freeI t p => do
    let .ptr ptr_val ← env.getAs p .ptr
    modifyTrace (free t ptr_val)
    return env
  | .loadE t eff p => do
    let .eff eff_trace ← env.getAs eff .eff
    let .ptr ptr_val ← env.getAs p .ptr
    let (val, trace) := load t ptr_val eff_trace
    setTrace trace
    return env.cons ⟨_, .data val⟩
  | .storeE t eff p x => do
    let .eff eff_trace ← env.getAs eff .eff
    let .ptr ptr_val ← env.getAs p .ptr
    let .data x_val ← env.getAs x (.data t)
    setTrace (store ptr_val x_val eff_trace)
    return env
  | .allocE t eff p => do
    let .eff eff_trace ← env.getAs eff .eff
    let .ptr ptr_val ← env.getAs p .ptr
    setTrace (alloc t ptr_val eff_trace)
    return env
  | .freeE t eff p => do
    let .eff eff_trace ← env.getAs eff .eff
    let .ptr ptr_val ← env.getAs p .ptr
    setTrace (free t ptr_val eff_trace)
    return env
  | .createEff => do
    let trace ← getTrace
    return env.cons ⟨_, .eff trace⟩
  | .consumeEff e => do
    let .eff trace ← env.getAs e .eff
    setTrace trace
    return env.remove e
where
  /-- Modify the current trace in the state. -/
  modifyTrace : (f : Trace τ → Trace τ) → ExecM τ Unit := modify
  /-- Modify the current trace in the state and return a value computed from the original trace. -/
  modifyGetTrace {α} : (f : Trace τ → α × Trace τ) → ExecM τ α := modifyGet
  /-- Get the current trace from the state. -/
  getTrace : ExecM τ (Trace τ) := get
  /-- Set the current trace in the state. -/
  setTrace : (es : Trace τ) → ExecM τ Unit := set


/-- Execute all instructions in a program sequentially, threading the environment through. -/
def Program.exec (env : Environment τ n) : (p : Program τ n) → ExecM τ (Environment τ p.results)
  | .nil => return env
  | .cons i p => do
    let env' ← i.exec env
    p.exec env'
