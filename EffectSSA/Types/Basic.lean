import EffectSSA.Assumptions.MemorySignature

/-!
# Typesystem Preliminaries
-/
namespace EffectSSA

/-!
## Types
--------------------------------------------------------------------------------
-/

/--
The type of all types (including both pointer and plain data types).
-/
inductive Ty.Typ (τ : Ty)
  /-- Type of pointers. -/
  | ptr
  /-- Type of effect traces. -/
  | eff
  /-- Plain data types. -/
  | data (d : τ.DType)

/-!
## Definitions
--------------------------------------------------------------------------------
-/

namespace Ty.Typ
variable {τ : Ty}

/--
A type is unrestricted if it is not linear.

N.B: `eff` is the only linear (i.e., not unrestricted) type
-/
def isUnrestricted : τ.Typ → Bool
  | eff => false
  | _ => true

/-- Plain data types may be coerced to arbitrary types. -/
instance : Coe τ.DType τ.Typ where coe := .data
