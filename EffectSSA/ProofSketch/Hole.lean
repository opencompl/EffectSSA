module

public import Lean.Elab.Tactic.Simp

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

def elim0 : Hole 0 → α := Fin.elim0

def fromId? {n} (h : HoleId) : Option (Hole n) :=
  if hr : h.toNat < n then
    some ⟨h.toNat, hr⟩
  else
    none

section Lemmas

@[simp, grind =]
theorem fromId?_id (h : Hole n) :
    (Hole.fromId? h.id) = some h := by
  simp [Hole.fromId?, Hole.id]

theorem eq_elim0 {α : Sort u} (f : Hole 0 → α) : f = Hole.elim0 :=
  funext fun h => h.elim0

end Lemmas
end Hole

/-!
### `Hole.elim0` normalization simproc
--------------------------------------------------------------------------------
-/
section Meta

open Lean Meta Simp Elab

/--
Normalize any lambda `fun (_ : Hole 0) => _` to `Hole.elim0`.

We restrict the pattern to *lambdas* (rather than arbitrary terms of type
`Hole 0 → α`) to avoid the simproc firing too often.
-/
simproc ↓ EffectSSA.ProofSketch.hole0_elim0_simproc
    (fun (_ : EffectSSA.ProofSketch.Hole 0) => _) := fun e => do
  let Expr.lam _ dom _ _ := e | return Step.continue
  unless ← isDefEq dom (mkApp (mkConst ``EffectSSA.ProofSketch.Hole) (mkNatLit 0)) do
    return Step.continue
  let Expr.forallE _ _ codomain _ ← inferType e | return Step.continue
  if codomain.hasLooseBVars then return Step.continue
  let u ← getLevel codomain
  let elim0 := mkApp (mkConst ``EffectSSA.ProofSketch.Hole.elim0 [u]) codomain
  let proof := mkApp2 (mkConst ``EffectSSA.ProofSketch.Hole.eq_elim0 [u]) codomain e
  return Step.done { expr := elim0, proof? := proof }

/-! Simple smoke test -/
example : (fun _ : Hole 0 => 1) = (fun _ => 2) := by simp

end Meta
