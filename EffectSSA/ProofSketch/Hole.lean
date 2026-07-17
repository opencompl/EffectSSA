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

structure HoleId where
  toNat : Nat
instance : ToString HoleId where toString h := s!"{h.toNat}"

/--
A `Hole n` is the name of a hole in a context which may include at most `n`
distinct holes. It therefore also identifies a particular sequence in an
`n`-ary pattern.

A `Hole n` is in some sense a meta-variable.
-/
def Hole n := Fin n
  deriving DecidableEq

/-!
## Hole API
--------------------------------------------------------------------------------
-/
namespace Hole

/--
Erase the intrinsic upper bound on a `Hole` index,
returning the raw underlying `HoleId`.
-/
def id (h : Hole n) : HoleId where
  toNat := h.val

abbrev elim0 : Hole 0 → α := Fin.elim0

def fromId? {n} (h : HoleId) : Option (Hole n) :=
  if hr : h.toNat < n then
    some ⟨h.toNat, hr⟩
  else
    none

end Hole
