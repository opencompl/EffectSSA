
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

variable (τ : Ty)

/-! ## MemorySignature -/

class MemorySignature where
  /-- Semantic domain of pointers. -/
  Ptr : Type
  /-- Semantic domain of plain data types. -/
  TVal : τ.DType → Type

namespace Ty
variable [MemorySignature τ]

abbrev Ptr : Type := MemorySignature.Ptr τ
abbrev TVal : τ.DType → Type := MemorySignature.TVal

end Ty
