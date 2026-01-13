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

/-! Show that `ExecM` is in fact a (lawful) monad. -/
section Monad
instance : Monad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : LawfulMonad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadState (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadStateOf (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance

instance : Monad (ExecM.TypeErrM) := by unfold ExecM.TypeErrM; infer_instance
end Monad
