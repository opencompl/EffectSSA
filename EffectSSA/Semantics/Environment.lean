import EffectSSA.Assumptions.MemoryModel

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

/-- A `τ.Val` is a value of arbitrary (bundled) type `t : τ.Typ`. -/
inductive Ty.Val τ [MemorySignature τ] where
  | ptr (p : τ.Ptr)
  | data {t} (x : τ.TVal t)
  | eff (t : Trace τ)

structure Semantics.Environment τ [MemoryModel τ] (n : Nat) where
  toVec : List.Vector τ.Val n

/-!
## Definitions
--------------------------------------------------------------------------------
-/
