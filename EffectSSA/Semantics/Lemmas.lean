import EffectSSA.Syntax
import EffectSSA.Semantics.Program

/-!
# Lemmas about semantics
-/
namespace EffectSSA
variable {τ} [LawfulMemoryModel τ]

/-!
## Unfoldings
--------------------------------------------------------------------------------
-/

/-! ### InstructionSeq -/
namespace InstructionSeq
variable {is : InstructionSeq τ}

@[simp, grind =] theorem execM_nil : execM env (@nil τ) = return env := rfl
@[simp, grind =] theorem execM_cons : execM env (i ;> is) = i.execM env >>= is.execM := rfl

@[simp, grind =_ ] theorem run_execM : (execM env is).run = exec env is := by rfl

@[simp, grind =] theorem exec_nil : exec env (@nil τ) es? = some (env, es?) := rfl
@[simp, grind =] theorem exec_cons : exec env (i ;> is) es? =
    (i.exec env es?).bind fun (env, es?) => is.exec env es? := by
  simp [exec, -run_execM]; rfl

end InstructionSeq

/-! ### Instruction -/
namespace Instruction
variable {t : τ.DType} {p x : Var}
variable {i : Instruction τ}

section Run
open execM
variable (es? : Option (Trace τ))

@[simp, grind =] theorem run_execM : (execM env i).run = exec env i := by rfl

@[simp, grind =] theorem run_modifyGetTrace {f : Trace τ → α × Trace τ} :
    (modifyGetTrace f).run es? = some (
      let p := f (es?.getD .ub)
      (p.1, some p.2)) := by rfl

@[simp, grind =] theorem run_modifyTrace {f : Trace τ → Trace τ} :
    (modifyTrace f).run es? = some (((), some <| f (es?.getD .ub))) := by rfl

@[grind =] theorem run_takeTrace :
    takeTrace.run es? = some (match es? with
      | none => (.ub, some .ub)
      | some es => (es, none)) := by rfl

@[grind =] theorem run_putTrace :
    (putTrace ds).run es? = some ((), match es? with
      | none => some ds
      | some _ => some .ub) := by rfl

end Run

open execM (modifyTrace)

@[simp, grind =] theorem execM_storeI :
    execM env (.storeI t p x) = do
      modifyTrace (Semantics.store (← env.getPtr? p) (← env.getData? x t))
      return env :=
  rfl

end Instruction

/-!
## Environment
--------------------------------------------------------------------------------
-/
namespace Semantics.Environment
variable {env : Environment τ}

/-! ### Grind lemmas -/

@[simp, grind =] theorem get?_snoc_zero :
    (env.snoc x).get? ⟨0⟩ = pure x := rfl

@[simp, grind =] theorem getAs?_snoc_zero :
    (env.snoc ⟨t, x⟩).getAs? ⟨0⟩ t = some x := by
  simp [getAs?]

@[simp, grind =] theorem get?_snoc_succ :
    (env.snoc x).get? (v + 1) = env.get? v := by
  simp [get?, snoc]

@[simp, grind =] theorem getAs?_snoc_succ :
    (env.snoc x).getAs? (v + 1) t = env.getAs? v t := by
  simp [getAs?]

@[simp, grind =] theorem getAs?_empty : (∅ : Environment τ).getAs? v t = none := by rfl

@[simp, grind =] theorem get?_ofList (env : List τ.Val) :
  (ofList env).get? x = env[x.toNat]? := by rfl


/-! ### limitTo? -/

@[simp, grind =] theorem limitTo?_nil : env.limitTo? [] = some ∅ := by rfl

/-! ### empty -/

@[simp, grind =] theorem toList_empty : (∅ : Environment τ).toList = [] := by rfl

/-! ### snoc -/

@[simp, grind =] theorem toList_snoc : (snoc env x).toList = x :: env.toList := by rfl

/-! ### WellTyped lemmas -/
variable {Γ : Context τ}

@[simp, grind .] theorem wellTyped_empty : WellTyped (τ := τ) ∅ ∅ := by grind

@[simp, grind .] theorem wellTyped_snoc {Γ : Context τ} {env : Environment τ} {x : τ.Val}
    (hΓ : WellTyped Γ env) (hx : x.1 = t):
    WellTyped (Γ <: t) (env.snoc x) := by
  constructor
  · grind
  · intro v u
    rcases v with ⟨⟨⟩|_⟩ <;> grind [getAs?]

@[simp, grind .]
theorem wellTyped_eraseVar {Γ : Context τ} {env : Environment τ} {v : Var} :
    WellTyped Γ env → WellTyped (Γ.eraseVar v) env := by
  grind

end Semantics.Environment

/-!
## Instruction Rewrites
--------------------------------------------------------------------------------
-/
namespace Instruction
open Semantics (Environment)
open execM
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
