import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Types
import EffectSSA.Syntax
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

/-! Traces, pointers and plain data values can be coerced into a generic value. -/
namespace Ty.Val
instance : Coe (Trace τ) τ.Val where coe := (⟨.eff, .eff ·⟩)
instance : Coe τ.Ptr τ.Val where coe := (⟨.ptr, .ptr ·⟩)
instance : CoeOut (τ.DVal t) τ.Val where coe := (⟨.data t, .data ·⟩)
end Ty.Val

/-!
Similarly, a typed value of the respective concrete type may be coerced into a
trace, pointer or plain data value, as appropriate.
-/
namespace Ty.TVal
instance : Coe (τ.TVal .eff) (Trace τ) where coe := fun (.eff e) => e
instance : Coe (τ.TVal .ptr) τ.Ptr where coe := fun (.ptr p) => p
instance : Coe (τ.TVal <| .data t) (τ.DVal t) where coe := fun (.data x) => x
end Ty.TVal



/-! ### Environment API -/
namespace Semantics.Environment

/-! #### Environment Getters -/

/--
`env.get? v` retrieves the (untyped) value environment `env` associates with
the variable `v`. Returns `none` if the variable does not exist.
-/
def get? (env : Environment τ) (v : Var) : Option τ.Val :=
  env.toList[v.toNat]?

/--
`env.get v` retrieves the (untyped) value environment `env` associates with
the variable `v`. Throws a TypErr if the variable does not exist.
-/
def get (env : Environment τ) (v : Var) : ExecM τ τ.Val :=
  StateT.lift (env.get? v)

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

/--
`env.getAs v t` retrieves the value environment `env` associates with a
variable `v`, and then attempts to coerce this to be a typed value of type `t`.
Throws a type error if `v` has a type different from `t`, or if `v` is not
present in the environment.

See also `Environment.getAs?`, which returns none instead.
-/
def getAs (env : Environment τ) (v : Var) (t : τ.Typ) : ExecM τ (τ.TVal t) :=
  StateT.lift (env.getAs? v t)

/-- Retrieve a pointer via `getAs`. -/
def getPtr (env : Environment τ) (v : Var) : ExecM τ τ.Ptr := env.getAs v .ptr

/-- Retrieve an effect trace via `getAs`. -/
def getEff (env : Environment τ) (v : Var) : ExecM τ (Trace τ) := env.getAs v .eff

/-- Retrieve a data value via `getAs`. -/
def getData (env : Environment τ) (v : Var) (t : τ.DType) : ExecM τ (τ.DVal t) :=
  env.getAs v (.data t)

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

end Semantics.Environment


/-!
## WellTyped
--------------------------------------------------------------------------------
-/
namespace Semantics.Environment

def WellTyped (Γ : Context τ) (env : Environment τ) : Prop :=
  ∀ (v : Var) (t : τ.Typ), Γ[v]? = some t ↔ (env.getAs? v t).isSome
