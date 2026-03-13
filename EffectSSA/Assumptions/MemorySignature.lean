
/-!

# Assumed Types

This file codifies the following types that are assumed (i.e., user-provided)
in the formalization:
* `DType`, the type of plain data types
* `Ptr`, the semantic domain of pointer
* `TVal`, the semantic domain of plain data types `t : DType`.

These are the basic assumptions needed to define `Event`s.

-/
namespace EffectSSA

structure Ty where
  /-- Plain Data types -/
  DType : Type
  [instDecidableEqDType : DecidableEq DType]

variable (τ : Ty)

/-! ## MemorySignature -/

class MemorySignature where
  /-- Semantic domain of pointers. -/
  Ptr : Type
  [instDecidableEqPtr : DecidableEq Ptr]

  /-- Semantic domain of plain data types. -/
  DVal : τ.DType → Type
  [instDecidableEqTVal : ∀ t, DecidableEq (DVal t)]

namespace Ty
variable [MemorySignature τ]

/-- `τ.Ptr` is a pointer value. -/
abbrev Ptr : Type := MemorySignature.Ptr τ

/-- `τ.DVal t` is a plain data value of type `t : τ.DType`. -/
abbrev DVal : τ.DType → Type := MemorySignature.DVal

attribute [instance] Ty.instDecidableEqDType
attribute [reducible, instance] MemorySignature.instDecidableEqPtr
attribute [reducible, instance] MemorySignature.instDecidableEqTVal

end Ty
