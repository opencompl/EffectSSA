
/-!
# Compatibility Notation Typeclass
-/
namespace EffectSSA

/--
`Compat α` is the typeclass which supports the notation `x ⌣ y`, where `x, y : α`.
That is, it's a convenience wrapper for `HCompat`.

The precise meaning of this relation is type-dependent, but it generally revolves
around some notion of commuting side-effects.
-/
class Compat (α : Type u) where
  /-- The compatibility relation: `x ⌣ y` -/
  compat : α → α → Prop

/--
`HCompat α β` is the typeclass which supports the notation `x ⌣ y`, where `x : α`
and `y : β`.

The precise meaning of this relation is type-dependent, but it generally revolves
around some notion of commuting side-effects.
-/
class HCompat (α : Type u) (β : Type v) where
  /-- The compatibility relation: `x ⌣ y` -/
  hCompat : α → β → Prop

@[inherit_doc] infixl:60 " ⌣ " => HCompat.hCompat

/-- An instance of `Compat` implies an instance of `HCompat` -/
instance [Compat α] : HCompat α α where
  hCompat := Compat.compat

/--
An abbreviation for `DecidableRel` of the (heterogeneous) compatibility
relation on `α` and `β`.
-/
abbrev DecidableHCompat (α β) [HCompat α β] := DecidableRel (· ⌣ · : α → β → Prop)

/-- An abbreviation for `DecidableRel` of the compatibility relation on `α`. -/
abbrev DecidableCompat (α) [Compat α] := DecidableHCompat α α

/-- An abbreviation for `Std.Symm` of the compatibility relation on `α`. -/
abbrev SymmCompat (α) [Compat α] := Std.Symm (· ⌣ · : α → α → Prop)

/-- A symmetric compatibility relation satisfies `a ⌣ b → b ⌣ a`. -/
@[symm] abbrev SymmCompat.symm {α} [Compat α] [SymmCompat α] (a b : α) : a ⌣ b → b ⌣ a :=
  Std.Symm.symm a b
