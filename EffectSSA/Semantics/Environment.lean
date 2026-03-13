import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Types
import EffectSSA.Syntax.Untyped
import EffectSSA.Semantics.ExecM

import Mathlib.Data.Vector.Basic

/-!
# Exection Environment

Define environment, a mapping from variables to values.

-/
namespace EffectSSA

/-!
## Types
--------------------------------------------------------------------------------
-/
variable (τ) [MemoryModel τ]

/--
`τ.TVal t` is a value of type `t : τ.Typ`, meaning that it may be a pointer,
effect trace, or plain data value.

See also `τ.DVal t`, which is a typed value of just plain data.
-/
inductive Ty.TVal : τ.Typ → Type where
  | ptr (p : τ.Ptr) : TVal .ptr
  | eff (t : Trace τ) : TVal .eff
  | data {t} (x : τ.DVal t) : TVal (.data t)

/-- A `τ.Val` is a value of arbitrary (bundled) type `t : τ.Typ`. -/
def Ty.Val : Type := Σ t, τ.TVal t
-- FIXME: maybe `Ty.Val` ought to be a structure? We'll evaluate later.

structure Semantics.Environment τ [MemoryModel τ] where
  ofList :: toList : List τ.Val

/-!
## Definitions
--------------------------------------------------------------------------------
-/
variable {τ}

/-! ### Val API -/
namespace Ty

/-! Traces, pointers and plain data values can be coerced into a generic value. -/
namespace Val
instance : Coe (Trace τ) τ.Val where coe := (⟨.eff, .eff ·⟩)
instance : Coe τ.Ptr τ.Val where coe := (⟨.ptr, .ptr ·⟩)
instance : CoeOut (τ.DVal t) τ.Val where coe := (⟨.data t, .data ·⟩)
end Val

/-!
Similarly, a typed value of the respective concrete type may be coerced into a
trace, pointer or plain data value, as appropriate.
-/
namespace TVal
instance : Coe (τ.TVal .eff) (Trace τ) where coe := fun (.eff e) => e
instance : Coe (τ.TVal .ptr) τ.Ptr where coe := fun (.ptr p) => p
instance : Coe (τ.TVal <| .data t) (τ.DVal t) where coe := fun (.data x) => x
end TVal

/-- Coerce a statically typed value into a dynamically typed value. -/
@[grind] abbrev TVal.toVal : τ.TVal t → τ.Val := (⟨t, ·⟩)

end Ty

/-! ### Environment API -/
namespace Semantics.Environment

/-!
`∅` represents the empty environment, without any values.
-/
instance : EmptyCollection (Environment τ) where
  emptyCollection := .ofList []

/-! #### size -/

@[simp, grind =]
abbrev size (env : Environment τ) : Nat := env.toList.length

/-! #### Environment Getters -/

/--
`env.get? v` retrieves the (untyped) value environment `env` associates with
the variable `v`. Returns `none` if the variable does not exist.
-/
def get? (env : Environment τ) (v : Var) : Option τ.Val :=
  env.toList[v.toNat]?

/--
`env.getAs? v t` retrieves the value environment `env` associates with the
variable `v`, and then attempts to coerce this to be a typed value of type `t`.
Returns `none` if `v` has a type different from `t`, or if `v` is not present in
the environment.
-/
def getAs? (env : Environment τ) (v : Var) (t : τ.Typ) : Option (τ.TVal t) := do
  let val ← env.get? v
  if h : val.1 = t then
    some <| h ▸ val.2
  else
    none

/-- Retrieve a pointer via `getAs?`. -/
@[simp, grind =]
def getPtr? (env : Environment τ) (v : Var) : Option τ.Ptr := env.getAs? v .ptr

/-- Retrieve an effect trace via `getAs`. -/
@[simp, grind =]
def getEff? (env : Environment τ) (v : Var) : Option (Trace τ) := env.getAs? v .eff

/-- Retrieve a data value via `getAs`. -/
@[simp, grind =]
def getData? (env : Environment τ) (v : Var) (t : τ.DType) : Option (τ.DVal t) :=
  env.getAs? v (.data t)

/-! #### Environment Constructors -/

/--
`env.snoc x` adds a new variable to environment `env` assigning value `x` to it.
-/
def snoc (x : τ.Val) (env : Environment τ) : Environment τ :=
  ⟨env.toList.cons x⟩

/-! #### Environment Modification -/

/--
`env.eraseVar v` removes a variable `v` from an environment `env`.
-/
def eraseVar (env : Environment τ) (v : Var) : Environment τ :=
  ⟨env.toList.eraseIdx v.toNat⟩

/-
TODO: #21 Fully erasing values from the environment feels a bit dangerous, at it loses
historical information. In particular, we lose the ability to phrase a CompCert-style
equation lemma, since we can no longer evaluate an old linear operation under a
more recent environment. Such an equation lemma might become very useful once we
start to consider rewrites...

For now, we really have to erase value from the environment, to match how linear
types are erased from the typing context; this essentially means that linear
variable indices get reused, so if we kept such variables around in the environment,
then the indices would get out of sync.

This could be fixed by refactoring a context to be a list of optional types,
rather than a straight list of types. Then, `Context.eraseVar` would set the
relevant type to `none`, rather than dropping it from the list. By doing so,
our variable indices would become more stable, and we would be able to keep
the "stale" values around in the context.

This would mean that our semantics no longer crashes on programs that violate
linearity, but this is not an issue; we really only care about the semantics of
well-formed programs, and linearity is easy enough to decide statically.
-/

/--
`env.limitTo vs` returns an environment containing just the variables `vs`, and
the values the original environment `env` assigns to these variables.
Returns `none` if any of the variables in `vs` are not present in `env`.

The variables are re-ordered in the process, so that the i-th variables of
the returned environment corresponds to `vs[i]`.
-/
def limitTo? (env : Environment τ) (vs : List Var) : Option (Environment τ) := do
  let xs ← vs.mapM (env.get? ·)
  return ofList xs

end Semantics.Environment


/-!
## WellTyped
--------------------------------------------------------------------------------
-/
namespace Semantics.Environment

@[grind =]
def WellTyped (Γ : Context τ) (env : Environment τ) : Prop :=
  ∀ (v : Var) (t : τ.Typ), Γ[v]? = some t ↔ (env.getAs? v t).isSome
