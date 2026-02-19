import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Trace

/-!
# `ExecM` Execution Monad

This file defines the `ExecM` monad in which programs and instructions will be
executed.
-/
namespace EffectSSA
variable (τ : Ty) [MemoryModel τ]

/-!
## Types
--------------------------------------------------------------------------------
-/

/-- `ExecM` is the monad in which programs are executed. -/
def ExecM := StateT (Option <| Trace τ) TypeErrM
  where
    /-- `TypeErrM α` represents either a type-error, or a value of type `α`. -/
    TypeErrM := Option

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace ExecM
variable {τ}

/-! Show that `ExecM` is in fact a (lawful) monad. -/
section Monad
instance : Monad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : LawfulMonad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadState (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadStateOf (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance

instance : Monad (ExecM.TypeErrM) := by unfold ExecM.TypeErrM; infer_instance
instance : LawfulMonad (ExecM.TypeErrM) := by unfold ExecM.TypeErrM; infer_instance

instance : MonadLift ExecM.TypeErrM (ExecM τ) := by unfold ExecM; infer_instance
end Monad


/--
Run an `ExecM` by providing a possibly missing initial trace.

This is assumed to represent a complete execution, so if a trace is not present
in the state by the end, UB is returned instead.
-/
def run' (x : ExecM τ α) (es? : Option (Trace τ)) : ExecM.TypeErrM (α × Trace τ) := do
  let ⟨ret, events?⟩ ← StateT.run x es?
  return ⟨ret, events?.getD .ub⟩

/--
Run an `ExecM` by providing an initial trace.

This is assumed to represent a complete execution, so if a trace is not present
in the state by the end, UB is returned instead.
-/
def run (x : ExecM τ α) (es : Trace τ) : ExecM.TypeErrM (α × Trace τ) := do
  run' x (some es)
