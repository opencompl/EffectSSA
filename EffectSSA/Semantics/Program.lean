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
  | .loadI t p => do
    let .ptr ptr_val ← env.getAs p .ptr
    let val ← modifyGetTrace (load t ptr_val)
    return env.cons val
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
    return env.cons val
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
    return env.cons trace
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
