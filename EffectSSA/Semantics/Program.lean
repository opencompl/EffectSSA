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
variable (τ : Ty) [MemoryModel τ]

-- From here on, `τ` will be implicit
variable {τ}

/--
Execute a single instruction `i` in a specific environment, returning a new
environment with the results of `i` added to it, and any linear values consumed
by `i` removed.
-/
def Instruction.exec (env : Environment τ n) : (i : Instruction τ n) → ExecM τ (Environment τ i.results)
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
    setTrace trace
    return env.snoc val
  | .storeE t eff p x => do
    setTrace (store (←env.getPtr p) (←env.getData x t) (←env.getEff eff))
    return env
  | .allocE t eff p => do
    setTrace (alloc t (←env.getPtr p) (←env.getEff eff))
    return env
  | .freeE t eff p => do
    setTrace (free t (←env.getPtr p) (←env.getEff eff))
    return env
  -- Effect state bookkeeping operations
  | .createEff => do
    let trace ← getTrace
    return env.snoc trace
  | .consumeEff e => do
    setTrace (←env.getEff e)
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
