module

/-!
# Denote typeclass

This file defines the `Denote` typeclass, which drives the `⟦·⟧` notation.
-/
public section

namespace EffectSSA

class Denote (α : Type u) (β : outParam (Type v)) where
  denote : α → β

notation "⟦" i "⟧" => Denote.denote i
