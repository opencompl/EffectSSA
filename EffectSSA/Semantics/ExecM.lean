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

/-- `ExecT` adds the mutable state needed to execute programs to a monad. -/
def ExecT := StateT (Option <| Trace τ)

abbrev ExecM := ExecT τ Option

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace ExecM
variable {τ}

/-! ### Instances -/

/-! Show that `ExecM` is in fact a (lawful) monad. -/
section Monad

instance : Monad (ExecM τ) := StateT.instMonad
instance : LawfulMonad (ExecM τ) := StateT.instLawfulMonad
instance : MonadState (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecT; infer_instance
instance : MonadStateOf (Option <| Trace τ) (ExecM τ) := by unfold ExecM ExecT; infer_instance

instance : MonadLift Option (ExecM τ) := StateT.instMonadLift
instance : LawfulMonadLift Option (ExecM τ) := StateT.instLawfulMonadLift
end Monad

/-! ### run -/

/--
Run an `ExecM` by providing a possibly missing initial trace.
-/
def run (x : ExecM τ α) (es? : Option (Trace τ)) : Option (α × Option (Trace τ)) := do
  StateT.run x es?

/-!
## Lemmas
--------------------------------------------------------------------------------
-/
section Lemmas

@[simp, grind =]
theorem run_liftM (x : Option α) (es?) :
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
