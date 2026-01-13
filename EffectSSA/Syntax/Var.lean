
/-!
# Variables

This file defines `Var n`, the type of program variables with an upper bound.

-/
namespace EffectSSA

/-!
## Var
--------------------------------------------------------------------------------
-/

/--
`Var n` is a de Bruijn index representing a variable, given an upper bound `n`
on the number of available variables.
-/
def Var n := Fin n

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace Var

/-- Return the underlying index of a variable. -/
def toFin (v : Var n) : Fin n := v
/-- Construct a variable from its index. -/
def ofFin (i : Fin n) : Var n := i

/-- The bound on a variable `Var n` may implicitly be weakened to `n + 1`. -/
instance : Coe (Var n) (Var <| n + 1) where coe := Fin.succ

end Var
