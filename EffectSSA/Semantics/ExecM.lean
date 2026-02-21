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

/-! ### Instances -/

/-! Show that `ExecM` is in fact a (lawful) monad. -/
section Monad
instance : Monad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : LawfulMonad (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadState (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance
instance : MonadStateOf (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecM.TypeErrM; infer_instance

instance : Monad (ExecM.TypeErrM) := by unfold ExecM.TypeErrM; infer_instance
instance : LawfulMonad (ExecM.TypeErrM) := by unfold ExecM.TypeErrM; infer_instance

instance : MonadLift ExecM.TypeErrM (ExecM τ) := by unfold ExecM; infer_instance
instance : LawfulMonadLift ExecM.TypeErrM (ExecM τ) := by unfold ExecM; infer_instance
end Monad

/-! ### run -/

/--
Run an `ExecM` by providing a possibly missing initial trace.
-/
def run (x : ExecM τ α) (es? : Option (Trace τ)) : ExecM.TypeErrM (α × Option (Trace τ)) := do
  StateT.run x es?

/-!
## Lemmas
--------------------------------------------------------------------------------
-/
section Lemmas

@[simp, grind =]
theorem run_liftM (x : ExecM.TypeErrM α) (es?) :
    run (τ:=τ) (liftM x) es? = (do
      let a ← x
      some (a, es?)) := by rfl

@[simp, grind =]
theorem run_bind (x : ExecM τ α) (es?) :
    (x >>= f).run es? = (do
      let p ← x.run es?
      (f p.fst).run p.snd) := by rfl

@[simp, grind =]
theorem run_map (f : α → β) (x : ExecM τ α) :
    (f <$> x).run es? = (fun p => (f p.fst, p.snd)) <$> x.run es? := StateT.run_map ..

end Lemmas
