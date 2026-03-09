import EffectSSA.Syntax.Typed
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas

/-!
# Intrinsically Typed Environments
-/
namespace EffectSSA
variable {τ} [MemoryModel τ]

structure Semantics.TEnvironment (Γ : Context τ) where
  env : Environment τ
  wt : env.WellTyped Γ := by grind

/-!
### Grind
-/
open Semantics (TEnvironment)

grind_pattern TEnvironment.wt => TEnvironment.env self


/-!
## Coercions
--------------------------------------------------------------------------------
The typed structures can be implicitly coerced into the underlying
untyped variants
-/
open Semantics (Environment TEnvironment)
variable {Γ : Context τ}

instance : CoeOut (TEnvironment Γ) (Environment τ) where coe := TEnvironment.env
instance : CoeOut (TVar Γ t) Var where coe := TVar.toVar

instance : CoeOut (TEnvironment Γ × α) (Environment τ × α) where
  coe p := (p.1.env, p.2)

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace Semantics.TEnvironment

def get (env : TEnvironment Γ) (v : TVar Γ t) : τ.TVal t :=
  env.env.getAs? v.toVar t |>.get <| by
    have := env.wt v
    grind

/--
Limit a typed environment to the given variables, yielding a smaller
-/
def limitTo (env : TEnvironment Γ) (vs : TVarList Γ ts) : TEnvironment ⟨ts⟩ where
  env := .ofList <| vs.map (env.get · |>.toVal)
  wt := by grind [Environment.getAs?, Environment.get?]

/-- Empty environment. -/
instance : EmptyCollection (TEnvironment (τ:=τ) ∅) where
  emptyCollection := { env := ∅ }

end Semantics.TEnvironment

/-!
## Lemmas
--------------------------------------------------------------------------------
-/

namespace Semantics.TEnvironment
variable {Γ : Context τ} (env : TEnvironment Γ)

@[simp, grind =] theorem length_toList_env : env.env.toList.length = Γ.size := by grind

-- getAs?

@[simp, grind =] theorem env_getAs?_isSome_eq :
    (env.env.getAs? v t).isSome = decide (Γ[v]? = some t) := by
  simp [env.wt v t]

@[simp, grind =] theorem env_getAs?_isSome :
    (env.env.getAs? v t).isSome ↔ Γ[v]? = some t := by
  simp

@[simp, grind =] theorem env_getAs?_eq (h : Γ[v]? = some t) (env : TEnvironment Γ) :
    (env.env.getAs? v t) = some (env.get ⟨v, h⟩) := by
  simp [get]

-- get?

open Ty (TVal) in
@[grind =>] theorem env_get?_eq_getAs?_of (h : Γ[v]? = some t) :
    env.env.get? v = TVal.toVal <$> env.env.getAs? v t := by
  have := (env.wt v _).mp h
  obtain ⟨x, hx⟩ : ∃ x, env.env.getAs? v t = some x := by grind
  simp only [hx, Option.map_eq_map, Option.map_some]
  simp only [Environment.getAs?, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.dite_none_right_eq_some, Option.some.injEq] at hx
  rcases hx with ⟨⟨t', x'⟩, hp₁, ⟨rfl, hp₂⟩⟩
  grind

@[simp, grind! .] theorem env_get?_eq (h : Γ[v]? = some t) (env : TEnvironment Γ) :
    (env.env.get? v) = some (env.get ⟨v, h⟩ |>.toVal) := by
  grind


@[simp, grind =] theorem env_empty : TEnvironment.env (τ:=τ) (∅ : TEnvironment ∅) = ∅ := by rfl

@[simp, grind =] theorem env_limitTo? (vs : TVarList Γ ts) :
    env.env.limitTo? vs.toList = some (env.limitTo vs).env := by
  -- FIXME: this should eventually be proven
  sorry
