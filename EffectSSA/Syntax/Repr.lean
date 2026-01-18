import EffectSSA.Syntax.Basic
import EffectSSA.Syntax.Var

/-!
# Printing of Syntax
This file defines how to print programs and instructions.
-/
namespace EffectSSA
variable {τ : Ty} [Repr τ.DType]
open Std (Format)

/-!
## VarPrintM
We first define a monad which keeps track of which variable names are currently
in scope: this is needed to properly translate de bruijn indices to consistent
names, while taking into account linear variables which have been consumed.
-/

structure VarPrintM.State where
  freeVars : List String := []
  vars : List String := []
  nextIndex : Nat := 0

def VarPrintM := StateM VarPrintM.State

/-! Boilerplate -/
namespace VarPrintM
instance : Monad VarPrintM := by unfold VarPrintM; infer_instance
instance : MonadState VarPrintM.State VarPrintM := by unfold VarPrintM; infer_instance
instance : MonadStateOf VarPrintM.State VarPrintM := by unfold VarPrintM; infer_instance

def run (x : VarPrintM α) : α := StateT.run' x {}

end VarPrintM

/-! ### printVar -/

def freshVarName : VarPrintM String := do
  modifyGet (fun (s : VarPrintM.State) =>
      let v := s!"x_{s.nextIndex}"
      (v, {s with
        nextIndex := s.nextIndex + 1
      })
    )

def printVar (v : Var) : VarPrintM String := do
  let { vars, .. } ← get
  let v := v.toNat
  if h : v < vars.length then
    return vars[v]
  else
    let newVars ← List.range (v - vars.length + 1)
      |>.mapM (fun _ => freshVarName)
    let newVars := newVars.reverse
    modify (fun s => {s with
      freeVars := s.freeVars ++ newVars
      vars := s.vars ++ newVars
    })
    return newVars.getLast!

def forgetVar (v : Var) : VarPrintM Unit := do
  modify (fun s => {s with vars := s.vars.eraseIdx v.toNat})

/-!
Add `n` new variables to the context, returning the user-facing names of these
new variables in a comma-seperated list.
-/
def printNewVars (n : Nat) : VarPrintM Format := do
  let vs ← (List.range n).mapM fun _ => do
    let v ← freshVarName
    modify (fun s => {s with vars := v :: s.vars})
    return v
  return f!",".joinSep vs

/-! ## printWith -/

def Instruction.printM : Instruction τ → VarPrintM Format
  -- Basic memory ops with implicit effects
  | loadI t p => do
    let p ← printVar p
    let r ← printNewVars 1
    return f!"{r} := loadI[{repr t}]({p})"
  | storeI t p x => do
    let p ← printVar p
    let x ← printVar x
    return f!"storeI[{repr t}]({p}, {x})"
  | allocI t p => do
    let p ← printVar p
    return f!"allocI[{repr t}]({p})"
  | freeI t p => do
    let p ← printVar p
    return f!"freeI[{repr t}]({p})"
  -- Basic memory ops in EffectSSA form
  | loadE t eff p => do
    let eff ← printVar eff
    let p ← printVar p
    let r ← printNewVars 2
    return f!"{r} := loadE[{repr t}]({eff}, {p})"
  | storeE t eff p x => do
    let eff ← printVar eff
    let p ← printVar p
    let x ← printVar x
    let r ← printNewVars 1
    return f!"{r} := storeE[{repr t}]({eff}, {p}, {x})"
  | allocE t eff p => do
    let eff ← printVar eff
    let p ← printVar p
    let r ← printNewVars 1
    return f!"{r} := allocE[{repr t}]({eff}, {p})"
  | freeE t eff p => do
    let eff ← printVar eff
    let p ← printVar p
    let r ← printNewVars 1
    return f!"{r} := freeE[{repr t}]({eff}, {p})"
  -- Effect Bookkeeping
  | split eff => do
    let eff ← printVar eff
    let r ← printNewVars 2
    return f!"{r} := split({eff})"
  | merge eff₁ eff₂ => do
    let eff₁ ← printVar eff₁
    let eff₂ ← printVar eff₂
    let r ← printNewVars 1
    return f!"{r} := merge({eff₁}, {eff₂})"
  | createEff => do
    let r ← printNewVars 1
    return f!"{r} := createEff"
  | consumeEff e => do
    let e ← printVar e
    return f!"consumeEff({e})"

def Program.printM (p : Program τ) : VarPrintM Format :=
  p.foldlM (fun f i => do return f ++ (← i.printM) ++ Format.line) Format.nil

/-! ## print -/

def Instruction.print (i : Instruction τ) : Format :=
  VarPrintM.run <| i.printM

def Program.print (p : Program τ) : Format :=
  VarPrintM.run <| p.printM

-- TODO: generate docstrings for printWith and print functions
--       the former should be more extensive, whereas the print may be more
--       succinct by referring to printWith.

/-!
## Repr
`Repr` instances are derived from the `print` functions.
-/
instance : Repr (Program τ) where reprPrec p _ :=
  VarPrintM.run <| do
    let p ← p.printM
    let { freeVars, .. } ← get
    let vs := f!",".joinSep freeVars
    return f!"program\{{vs}}(" ++ Format.line ++ Format.nest 2 p ++ Format.line ++ f!")"

end EffectSSA
