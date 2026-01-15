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

def printVar (v : Var n) : VarPrintM String := do
  let vs ← get
  -- dbg_trace "Printing variable {v.toNat} with state {vs.vars}"
  return match vs.vars[v.toNat]? with
  | some x => x
  | none => "{failed to print variable}"

def forgetVar (v : Var n) : VarPrintM Unit := do
  modify (fun s => {s with
    vars := s.vars.eraseIdx v.toFin
  })

/-!
Add `n` new variables to the context, returning the user-facing names of these
new variables in a comma-seperated list.
-/
def printNewVars (n : Nat) : VarPrintM Format := do
  let vs ← (List.range n).mapM fun _ => do
    modifyGet (fun (s : VarPrintM.State) =>
      let v := s!"x_{s.nextIndex}"
      (v, {s with
        vars := v :: s.vars,
        nextIndex := s.nextIndex + 1
      })
    )
  return f!",".joinSep vs

/-! ## printWith -/

def Instruction.printM : Instruction τ n → VarPrintM Format
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

def Program.printM : Program τ n → VarPrintM Format
  | .nil => return Format.nil
  | .cons i p => do
    return (← i.printM) ++ Format.line ++ (← p.printM)

/-! ## print -/

def Instruction.print (i : Instruction τ n) : Format :=
  VarPrintM.run <| do
    let _ ← printNewVars n
    i.printM

def Program.print (p : Program τ n) : Format :=
  VarPrintM.run <| do
    let _ ← printNewVars n
    p.printM

-- TODO: generate docstrings for printWith and print functions
--       the former should be more extensive, whereas the print may be more
--       succinct by referring to printWith.

/-!
## Repr
`Repr` instances are derived from the `print` functions.
-/
instance : Repr (Program τ n) where reprPrec p _ :=
  VarPrintM.run <| do
    let vs ← printNewVars n
    let p ← p.printM
    return f!"program\{{vs}}(" ++ Format.line ++ Format.nest 2 p ++ Format.line ++ f!")"

end EffectSSA
