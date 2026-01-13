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
end Monad

end ExecM

variable {τ}

-- def Environment.getAs (env : Environment _ _) (v : Var n) (t : τ.Ty) : τ.TVal t :=
--   sorry

/--
Execute a single instruction `i` in a specific environment, returning a new
environment with the results of `i` added to it, and any linear values consumed
by `i` removed.
-/
def Instruction.exec (env : Environment τ n) : (i : Instruction τ n) → ExecM τ (Environment τ i.results)
  -- FIXME: the following code is very verbose and messy, it should be cleaned up
  --        and made more succinct by introducing a helper like `Environment.getAs`
  | .loadI t p => fun es => do
    let .ptr ptr_val := env.toVec.get p | none
    let (val, trace) := load t ptr_val es
    some (⟨env.toVec.cons (.data val)⟩, trace)
  | .storeI t p x => fun es => do
    let .ptr ptr_val := env.toVec.get p | none
    let .data x_val := env.toVec.get x | none
    let trace := store ptr_val x_val es
    some (env, trace)
  | .allocI t p => fun es => do
    let .ptr ptr_val := env.toVec.get p | none
    let trace := alloc t ptr_val es
    some (env, trace)
  | .freeI t p => fun es => do
    let .ptr ptr_val := env.toVec.get p | none
    let trace := free t ptr_val es
    some (env, trace)
  | .loadE t eff p => fun _ => do
    let .eff eff_trace := env.toVec.get eff | none
    let .ptr ptr_val := env.toVec.get p | none
    let (val, trace) := load t ptr_val eff_trace
    some (⟨env.toVec.cons (.data val)⟩, trace)
  | .storeE t eff p x => fun _ => do
    let .eff eff_trace := env.toVec.get eff | none
    let .ptr ptr_val := env.toVec.get p | none
    let .data x_val := env.toVec.get x | none
    let trace := store ptr_val x_val eff_trace
    some (env, trace)
  | .allocE t eff p => fun _ => do
    let .eff eff_trace := env.toVec.get eff | none
    let .ptr ptr_val := env.toVec.get p | none
    let trace := alloc t ptr_val eff_trace
    some (env, trace)
  | .freeE t eff p => fun _ => do
    let .eff eff_trace := env.toVec.get eff | none
    let .ptr ptr_val := env.toVec.get p | none
    let trace := free t ptr_val eff_trace
    some (env, trace)
  | .createEff => fun trace =>
    some (⟨env.toVec.cons (.eff trace)⟩, trace)
  | .consumeEff e => fun _ => do
    let .eff trace := env.toVec.get e | none
    -- TODO: Implement removal of linear variable e from environment
    sorry

/-- Execute all instructions in a program sequentially, threading the environment through. -/
def Program.exec (env : Environment τ n) : (p : Program τ n) → ExecM τ (Environment τ p.results)
  | .nil => return env
  | .cons i p => do
    let env' ← i.exec env
    p.exec env'
