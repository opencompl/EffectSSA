module


/-!
# Holes

This file defines a notion of named "hole" variables.
In particular, there is:
* `Hole n`: the type of intrinsically well-scoped hole variables, and
* `HoleId`: the type of raw, unscoped hole variable ids.
-/
@[expose] public section
namespace EffectSSA.ProofSketch

/-!
## Types
--------------------------------------------------------------------------------
-/

@[grind cases]
structure HoleId where
  toNat : Nat
deriving DecidableEq
instance : ToString HoleId where toString h := s!"{h.toNat}"

/--
A `Hole n` is the name of a hole in a context which may include at most `n`
distinct holes. It therefore also identifies a particular sequence in an
`n`-ary pattern.

A `Hole n` is in some sense a meta-variable.
-/
@[grind cases]
structure Hole (n : Nat) where
  /--
  Erase the intrinsic upper bound on a `Hole` index,
  returning the raw underlying `HoleId`.
  -/
  id : HoleId
  lt : id.toNat < n
deriving DecidableEq

/-!
## HoleId API
--------------------------------------------------------------------------------
-/
namespace HoleId

instance : OfNat HoleId n where
  ofNat := ⟨n⟩

instance : HAdd HoleId Nat HoleId where
  hAdd h n := ⟨h.toNat + n⟩

section Lemmas

@[simp, grind =] theorem toNat_ofNat (n : Nat) :
  (OfNat.ofNat n : HoleId).toNat = n := rfl

@[simp, grind =] theorem toNat_add (h : HoleId) (n : Nat) :
  (h + n).toNat = h.toNat + n := rfl

end Lemmas
end HoleId

/-!
## Hole API
--------------------------------------------------------------------------------
-/
namespace Hole
attribute [grind .] Hole.lt

abbrev toNat (h : Hole n) : Nat := h.id.toNat
def toFin (h : Hole n) : Fin n := ⟨h.toNat, by grind⟩

def fromId? {n} (h : HoleId) : Option (Hole n) :=
  if hr : h.toNat < n then
    some ⟨h, hr⟩
  else
    none

def elim0 (h : Hole 0) : α :=
  h.toFin.elim0

section Lemmas

@[simp, grind =] theorem val_toFin (h : Hole n) : h.toFin.val = h.toNat := rfl

@[simp, grind =]
theorem fromId?_id (h : Hole n) :
    (Hole.fromId? h.id) = some h := by
  grind [Hole.fromId?]

end Lemmas
end Hole
