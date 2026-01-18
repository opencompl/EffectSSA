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
def Var := Nat

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace Var

/-- Return the underlying index of a variable. -/
def toNat (v : Var) : Nat := v
/-- Construct a variable from its index. -/
def ofNat (i : Nat) : Var := i

def succ (v : Var) : Var := ofNat (v.toNat + 1)

/-!
### Metaprogramming API
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
