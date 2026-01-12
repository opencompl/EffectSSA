
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

def toFin (v : Var n) : Fin n := v
def ofFin (i : Fin n) : Var n := i

end Var
