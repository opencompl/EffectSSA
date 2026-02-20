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

/-! ### Grind lemmas -/

@[simp, grind =] theorem get?_snoc_zero :
    (env.snoc x).get? ⟨0⟩ = pure x := rfl

@[simp, grind =] theorem getAs_snoc_zero :
    (env.snoc ⟨t, x⟩).getAs ⟨0⟩ t = pure x := by
  simp [getAs, getAs?]

@[simp, grind =] theorem getAs?_empty : (∅ : Environment τ).getAs? v t = none := by rfl

@[simp, grind =] theorem get?_ofList (env : List τ.Val) :
  (ofList env).get? x = env[x.toNat]? := by rfl

/-! ### WellTyped lemmas -/
variable {Γ : Context τ}

@[simp, grind .]
theorem wellTyped_empty : WellTyped (τ := τ) ∅ ∅ := by simp [WellTyped]

/--
If a context `env` is well-typed w.r.t. a context `Γ`, then `env` has precisely
as many variables as `Γ` has types.
-/
@[grind →] theorem size_eq_of_wellTyped (wt : WellTyped Γ env) : env.size = Γ.size := by
  rcases env with ⟨env⟩
  rcases Γ with ⟨Γ⟩
  simp [WellTyped, getAs?] at wt
  simp [Environment.size, Context.size]
  induction Γ generalizing env
  case nil =>
    simp only [List.length_nil, List.length_eq_zero_iff]
    ext i
    specialize wt ⟨i⟩
    simp_all
  case cons t Γ ih =>
    show env.length = Γ.length + 1
    cases env
    case nil =>
      exfalso; simpa using wt ⟨0⟩ t
    case cons x env =>
      suffices env.length = Γ.length by simpa
      apply ih
      intro v t
      specialize wt (v + 1) t
      grind

@[grind →]
theorem isSome_get?_of_wellTyped (wt : WellTyped Γ env) :
    ∀ x, Γ[x]?.isSome → (env.get? x).isSome := by
  cases env; grind

@[grind <=]
theorem isSome_get_of_wellTyped {Γ} {env : Environment τ} (wt : WellTyped Γ env) :
    ∀ x, Γ[x]?.isSome → (env.get x).isSome :=
  isSome_get?_of_wellTyped wt

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

/-!
## Execution Lemmas
--------------------------------------------------------------------------------
-/
section WellTypedExec
open Semantics (Environment)
variable {p : Program τ} {Γ ts}

theorem Program.isSome_exec_of_wellTyped {env : Environment τ}
    (wt_p : p.WellTyped Γ ts)
    (wt_env : env.WellTyped Γ) :
    (p.exec env es).isSome := by
  rcases wt_p with ⟨Δ, wt_p, h_un, h_ts⟩
  rcases p with ⟨p, returnVars⟩
  simp_all only [Program.exec, Program.execM]
  induction wt_p generalizing env
  case nil Γ _ h =>
    subst h
    simp_all only [InstructionSeq.execM_nil, pure_bind, ExecM.run'_some]
    rw [mapM_liftM, ExecM.run_liftM, Option.map_eq_map, Option.isSome_map, isSome_mapM_iff]
    intro x hx
    have : ∃ (i : _) (hi : i < returnVars.length), returnVars[i] = x := List.mem_iff_getElem.mp hx
    have : Γ[x]?.isSome := by grind
    grind
  case cons x xs ih =>
    simp_all
    /-
    TODO:
    This requires verification of monadic code, which is going to be a pain.
    I'll leave this sorry for now, but I want to experiment with building an
    intrinsically well-typed data-structure on top of the untyped one, and then
    defining the semantics only for well-typed programs.
    Or at least, defining intrinsically well-typed exec functions defined in
    terms of the untyped ones + a lemma like this one.
    -/
    sorry
where
  mapM_liftM {α β m n} [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n] [LawfulMonad m] [LawfulMonad n]
      (xs : List α) (f : α → m β) :
      (xs.mapM fun x => liftM (n:=n) (f x)) = liftM (xs.mapM f) := by
    induction xs <;> simp_all
  isSome_mapM_iff {α β} (xs : List α) (f : α → Option β) :
      (xs.mapM f).isSome = ∀ x ∈ xs, (f x).isSome := by
    induction xs
    case nil => simp
    case cons x xs ih =>
      simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, List.mem_cons,
        forall_eq_or_imp]
      cases f x
      · simp_all
      · cases hfx : (List.mapM f xs) <;> simp_all

theorem Program.isSome_execClosed_of_wellTyped (wt : p.WellTyped ∅ ts) :
    p.execClosed.isSome := by
  apply isSome_exec_of_wellTyped wt
  simp
