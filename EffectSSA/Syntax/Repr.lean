import EffectSSA.Syntax.Basic
import EffectSSA.Syntax.Var

/-!
# Printing of Syntax
This file defines how to print programs and instructions.
-/
namespace EffectSSA
variable {τ : Ty} [Repr τ.DType]
open Std (Format)

/-! ## printWith -/

def Instruction.printWith (printVar : Nat → String) : Instruction τ n → Format
  -- Basic memory ops with implicit effects
  | loadI t p => f!"{printVar 0} := loadI[{repr t}]({printVar p.toNat})"
  | storeI t p x => f!"storeI[{repr t}]({printVar p.toNat}, {printVar x.toNat})"
  | allocI t p => f!"allocI[{repr t}]({printVar p.toNat})"
  | freeI t p => f!"freeI[{repr t}]({printVar p.toNat})"
  -- Basic memory ops in EffectSSA form
  | loadE t eff p => f!"{printVar 1}, {printVar 0} := loadE[{repr t}]({printVar eff.toNat}, {printVar p.toNat})"
  | storeE t eff p x => f!"{printVar 0} := storeE[{repr t}]({printVar eff.toNat}, {printVar p.toNat}, {printVar x.toNat})"
  | allocE t eff p => f!"{printVar 0} := allocE[{repr t}]({printVar eff.toNat}, {printVar p.toNat})"
  | freeE t eff p => f!"{printVar 0} := freeE[{repr t}]({printVar eff.toNat}, {printVar p.toNat})"
  -- Effect Bookkeeping
  | split eff => f!"{printVar 1}, {printVar 0} := split({printVar eff.toNat})"
  | merge eff₁ eff₂ => f!"{printVar 0} := merge({printVar eff₁.toNat}, {printVar eff₂.toNat})"
  | createEff => f!"{printVar 0} := createEff"
  | consumeEff e => f!"consumeEff({printVar e.toNat})"

def Program.printWith (printVar : Nat → String) : Program τ n → Format
  | .nil => Format.nil
  | .cons i p =>
      (i.printWith printVar) ++ Format.line ++ (p.printWith printVar)

/-! ## print -/

private def printVar : Nat → String := (s!"x_{·}")

def Instruction.print : Instruction τ n → Format := printWith printVar
def Program.print : Program τ n → Format := printWith printVar

-- TODO: generate docstrings for printWith and print functions
--       the former should be more extensive, whereas the print may be more
--       succinct by referring to printWith.

/-!
## Repr
`Repr` instances are derived from the `print` functions.
-/
instance : Repr (Program τ n) where reprPrec p _ :=
  let vs := (List.range n).map printVar
  let vs := Format.joinSep vs (";" ++ Format.line)
  let p := p.print
  f!"program\{{vs}}(" ++ Format.line ++ Format.nest 2 p ++ Format.line ++ ")"

end EffectSSA
