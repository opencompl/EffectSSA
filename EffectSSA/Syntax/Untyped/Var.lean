import Lean
import Qq

/-!
# Variables

This file defines `Var`, the type of program variables with an upper bound.

-/
namespace EffectSSA

/-!
## Var
--------------------------------------------------------------------------------
-/

/--
`Var` is a de Bruijn index representing a variable, given an upper bound `n`
on the number of available variables.
-/
@[grind]
structure Var where
  ofNat :: toNat : Nat
  deriving DecidableEq

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace Var

instance : HAdd Var Nat Var where
  hAdd v n := Var.ofNat (v.toNat + n)
instance : HSub Var Nat Var where
  hSub v n := Var.ofNat (v.toNat - n)

@[grind] instance : LT Var where lt v w := v.toNat < w.toNat
@[grind] instance : LE Var where le v w := v.toNat ≤ w.toNat
instance : DecidableRel ((· < ·) : Var → Var → Prop) := by
  intro v w; show Decidable (v.toNat < w.toNat); infer_instance
instance : DecidableRel ((· ≤ ·) : Var → Var → Prop) := by
  intro v w; show Decidable (v.toNat ≤ w.toNat); infer_instance


/-!
## Lemmas
--------------------------------------------------------------------------------
-/

@[ext]
theorem toNat_ext {v w : Var} (h : v.toNat = w.toNat) : v = w := by
  cases v; cases w; simpa using h

@[simp] theorem toNat_ofNat (i : Nat) : (Var.ofNat i).toNat = i := rfl
@[simp, grind =] theorem toNat_add (v : Var) (n : Nat) : (v + n).toNat = v.toNat + n := rfl
@[simp, grind =] theorem toNat_sub (v : Var) (n : Nat) : (v - n).toNat = v.toNat - n := rfl

@[simp, grind =] theorem ofNat_add (i n : Nat) : Var.ofNat (i + n) = (Var.ofNat i) + n := rfl
@[simp, grind =] theorem ofNat_sub (i n : Nat) : Var.ofNat (i - n) = (Var.ofNat i) - n := rfl

/-!
## Metaprogramming API
--------------------------------------------------------------------------------
-/
section Meta
open Lean Qq

instance : Lean.ToExpr Var where
  toExpr v :=
    let i : Q(Nat) := toExpr v.toNat
    q(Var.ofNat $i)
  toTypeExpr := q(Var)

end Meta

end Var
