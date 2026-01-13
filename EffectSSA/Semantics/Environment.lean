import EffectSSA.Assumptions.MemoryModel
import EffectSSA.Types
import EffectSSA.Syntax

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

/--
`τ.TVal t` is a value of type `t : τ.Typ`, meaning that it may be a pointer,
effect trace, or plain data value.

See also `τ.DVal t`, which is a typed value of just plain data.
-/
inductive Ty.TVal (τ) [MemorySignature τ] : τ.Typ → Type where
  | ptr (p : τ.Ptr) : τ.TVal .ptr
  | eff (t : Trace τ) : τ.TVal .eff
  | data {t} (x : τ.DVal t) : τ.TVal (.data t)

/-- A `τ.Val` is a value of arbitrary (bundled) type `t : τ.Typ`. -/
def Ty.Val τ [MemorySignature τ] := Σ t, τ.TVal t
-- FIXME: maybe `Ty.Val` ought to be a structure? We'll evaluate later.

structure Semantics.Environment τ [MemoryModel τ] (n : Nat) where
  toVec : List.Vector τ.Val n

/-!
## Definitions
--------------------------------------------------------------------------------
-/

namespace Semantics
variable {τ} [MemoryModel τ]

/--
`env.getAs? v t` retrieves the value environment `env` associates with a
variable `v`, and then attempts to coerce this to be a typed value of type `t`.
Returns `none` if `v` has a type different from `t`.
-/
def Environment.getAs? (env : Environment τ n) (v : Var n) (t : τ.Typ) : Option (τ.TVal t) :=
  -- TODO: generate
  sorry
