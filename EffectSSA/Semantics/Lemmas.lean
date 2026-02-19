import EffectSSA.Syntax
import EffectSSA.Semantics.Program

/-!
# Lemmas about semantics
-/
namespace EffectSSA
variable {τ} [MemoryModel τ]

/-!
## Unfoldings
--------------------------------------------------------------------------------
-/

/-! ### InstructionSeq -/
namespace InstructionSeq
variable {p : InstructionSeq τ}

@[simp, grind =] theorem execM_nil : execM env (@nil τ) = return env := rfl
@[simp, grind =] theorem execM_cons : execM env (i ;> p) = i.exec env >>= p.execM := rfl

end InstructionSeq

/-! ### Instruction -/
namespace Instruction
variable {t : τ.DType} {p x : Var}

open exec (modifyTrace)

@[simp, grind =] theorem exec_storeI :
    exec env (.storeI t p x) = do
      modifyTrace (Semantics.store (← env.getPtr p) (← env.getData x t))
      return env :=
  rfl

end Instruction

/-!
## Environment
--------------------------------------------------------------------------------
-/
namespace Semantics.Environment
variable {env : Environment τ}

@[simp, grind =]
theorem get?_snoc_zero : (env.snoc x).get? ⟨0⟩ = pure x := rfl

@[simp, grind =]
theorem getAs_snoc_zero : (env.snoc ⟨t, x⟩).getAs ⟨0⟩ t = pure x := by
  simp [getAs, getAs?]; rfl

end Semantics.Environment

/-!
## Instruction Rewrites
--------------------------------------------------------------------------------
-/
namespace Instruction
open Semantics (Environment)
open exec
variable {es es' : Trace τ}

@[simp, grind =] theorem run_takeTrace_some :
    StateT.run (@takeTrace τ _) (some es) = pure (es, none) := rfl
@[simp, grind =] theorem run_takeTrace_none :
    StateT.run (@takeTrace τ _) none = pure (.ub, some .ub) := rfl

@[simp, grind =] theorem run_putTrace_some :
    StateT.run (putTrace es) (some es') = pure ((), some .ub) := rfl
@[simp, grind =] theorem run_putTrace_none :
    StateT.run (putTrace es) none = pure ((), some es) := rfl

end Instruction
