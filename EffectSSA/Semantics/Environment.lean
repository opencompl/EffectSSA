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

structure Semantics.Environment τ [MemoryModel τ] (n : Nat) where
  toVec : List.Vector τ.Val n

/-!
## Definitions
--------------------------------------------------------------------------------
-/
variable {τ}

/-! ### Val API -/
namespace Ty.Val

/-! Traces, pointers and plain data values can be coerced into a generic value. -/
instance : Coe (Trace τ) τ.Val where coe := (⟨.eff, .eff ·⟩)
instance : Coe τ.Ptr τ.Val where coe := (⟨.ptr, .ptr ·⟩)
instance : CoeOut (τ.DVal t) τ.Val where coe := (⟨.data t, .data ·⟩)

end Ty.Val

/-! ### Environment API -/
namespace Semantics.Environment

/--
`env.getAs? v t` retrieves the value environment `env` associates with a
variable `v`, and then attempts to coerce this to be a typed value of type `t`.
Returns `none` if `v` has a type different from `t`.
-/
def getAs? (env : Environment τ n) (v : Var n) (t : τ.Typ) : Option (τ.TVal t) :=
  -- TODO: generate
  sorry

/--
`env.getAs v t` retrieves the value environment `env` associates with a
variable `v`, and then attempts to coerce this to be a typed value of type `t`.
Throws a type error if `v` has a type different from `t`.

See also `Environment.getAs?`, which returns none instead.
-/
def getAs (env : Environment τ n) (v : Var n) (t : τ.Typ) : ExecM τ (τ.TVal t) :=
  StateT.lift (env.getAs? v t)

/--
Create a new environment by prepending a value to the front of an environment.
-/
def cons (v : τ.Val) (env : Environment τ n) : Environment τ (n + 1) :=
  -- Prepends `v` to the environment, making it the new variable 0
  sorry

/--
Create a new environment by removing the variable at position `v` from the environment.
The result type matches `Instruction.results` for `consumeEff`.
-/
def remove (env : Environment τ n) (v : Var n) : Environment τ ((n : Int) + -1).toNat :=
  -- Removes the variable at position `v`, shifting all subsequent variables down
  sorry
