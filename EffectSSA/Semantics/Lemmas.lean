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

@[grind =] theorem get?_eraseVar :
    (env.eraseVar w).get? v = env.get? (if v.toNat < w.toNat then v else v + 1) := by
  grind [get?, eraseVar]

@[grind =] theorem getAs?_eraseVar :
    (env.eraseVar w).getAs? v t = env.getAs? (if v.toNat < w.toNat then v else v + 1) t := by
  grind [getAs?]

/-! ### limitTo? -/

@[simp, grind =] theorem limitTo?_nil : env.limitTo? [] = some ∅ := by rfl

/-! ### WellTyped lemmas -/
variable {Γ : Context τ}

@[simp, grind .] theorem wellTyped_empty : WellTyped (τ := τ) ∅ ∅ := by simp [WellTyped]

@[simp, grind .] theorem wellTyped_snoc {Γ : Context τ} {env : Environment τ} {x : τ.Val}
    (hΓ : WellTyped Γ env) (hx : x.1 = t):
    WellTyped (Γ <: t) (env.snoc x) := by
  intro v u
  rcases v with ⟨⟨⟩|_⟩ <;> grind [getAs?]

@[simp, grind .]
theorem wellTyped_eraseVar {Γ : Context τ} {env : Environment τ} {v : Var}
    (hΓ : WellTyped Γ env) :
    WellTyped (Γ.eraseVar v) (env.eraseVar v) := by
  grind

/--
If a context `env` is well-typed w.r.t. a context `Γ`, then `env` has precisely
as many variables as `Γ` has types.
-/
@[grind →] theorem size_eq_of_wellTyped (wt : WellTyped Γ env) : env.size = Γ.size := by
  rcases env with ⟨env⟩
  rcases Γ with ⟨Γ⟩
  simp only [size, Context.size]
  induction Γ generalizing env
  case nil =>
    simp only [List.length_nil, List.length_eq_zero_iff]
    ext i
    specialize wt ⟨i⟩
    simp_all [getAs?]
  case cons t Γ ih =>
    show env.length = Γ.length + 1
    cases env
    case nil =>
      exfalso; simpa [getAs?] using wt ⟨0⟩ t
    case cons x env =>
      suffices env.length = Γ.length by simpa
      apply ih
      intro v t
      specialize wt (v + 1) t
      grind [getAs?]

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

/-!
## Execution Lemmas
--------------------------------------------------------------------------------
-/
section WellTypedExec
open Semantics (Environment)
variable {p : Program τ} {Γ ts}

-- theorem Program.isSome_exec_of_wellTyped {env : Environment τ}
--     (wt_p : p.WellTyped Γ ts)
--     (wt_env : env.WellTyped Γ) :
--     (p.exec env es).isSome := by
--   rcases wt_p with ⟨Δ, wt_p, h_un, h_ts⟩
--   rcases p with ⟨p, returnVars⟩
--   simp_all only [Program.exec, Program.execM]
--   induction wt_p generalizing env
--   case nil Γ _ h =>
--     subst h
--     simp_all only [InstructionSeq.execM_nil, pure_bind, ExecM.run'_some]
--     rw [mapM_liftM, ExecM.run'_liftM, Option.map_eq_map, Option.isSome_map, isSome_mapM_iff]
--     intro x hx
--     have : ∃ (i : _) (hi : i < returnVars.length), returnVars[i] = x := List.mem_iff_getElem.mp hx
--     have : Γ[x]?.isSome := by grind
--     grind
--   case cons x xs ih =>
--     simp_all
--     /-
--     TODO:
--     This requires verification of monadic code, which is going to be a pain.
--     I'll leave this sorry for now, but I want to experiment with building an
--     intrinsically well-typed data-structure on top of the untyped one, and then
--     defining the semantics only for well-typed programs.
--     Or at least, defining intrinsically well-typed exec functions defined in
--     terms of the untyped ones + a lemma like this one.
--     -/
--     sorry
-- where
--   mapM_liftM {α β m n} [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n] [LawfulMonad m] [LawfulMonad n]
--       (xs : List α) (f : α → m β) :
--       (xs.mapM fun x => liftM (n:=n) (f x)) = liftM (xs.mapM f) := by
--     induction xs <;> simp_all
--   isSome_mapM_iff {α β} (xs : List α) (f : α → Option β) :
--       (xs.mapM f).isSome = ∀ x ∈ xs, (f x).isSome := by
--     induction xs
--     case nil => simp
--     case cons x xs ih =>
--       simp only [List.mapM_cons, Option.pure_def, Option.bind_eq_bind, List.mem_cons,
--         forall_eq_or_imp]
--       cases f x
--       · simp_all
--       · cases hfx : (List.mapM f xs) <;> simp_all

-- theorem Program.isSome_execClosed_of_wellTyped (wt : p.WellTyped ∅ ts) :
--     p.execClosed.isSome := by
--   apply isSome_exec_of_wellTyped wt
--   simp
