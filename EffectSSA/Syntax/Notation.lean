import EffectSSA.Syntax.Basic
import EffectSSA.Meta.Trace

import Lean
import Qq

/-!
# Program Syntax Notation

This file establishes a convenient notation for writing programs.
-/
namespace EffectSSA
namespace Parser

/-!
## Syntax
--------------------------------------------------------------------------------
-/

/-- Syntax category of EffectSSA instructions. -/
declare_syntax_cat ssa_instruction
section Instructions

-- Memory operations with implicit side effects (I suffix)
syntax ident ":=" "loadI" "[" term "]" "(" ident ")" : ssa_instruction
syntax "storeI" "[" term "]" "(" ident "," ident ")" : ssa_instruction
syntax "allocI" "[" term "]" "(" ident ")" : ssa_instruction
syntax "freeI" "[" term "]" "(" ident ")" : ssa_instruction

-- Memory operations in EffectSSA form (E suffix)
syntax ident "," ident ":=" "loadE" "[" term "]" "(" ident "," ident ")" : ssa_instruction
syntax ident ":=" "storeE" "[" term "]" "(" ident "," ident "," ident ")" : ssa_instruction
syntax ident ":=" "allocE" "[" term "]" "(" ident "," ident ")" : ssa_instruction
syntax ident ":=" "freeE" "[" term "]" "(" ident "," ident ")" : ssa_instruction

-- Effect bookkeeping operations
syntax ident "," ident ":=" "split" "(" ident ")" : ssa_instruction
syntax ident ":=" "merge" "(" ident "," ident ")" : ssa_instruction
syntax ident ":=" "createEff" : ssa_instruction
syntax "consumeEff" "(" ident ")" : ssa_instruction

end Instructions

/-- Syntax of EffectSSA Programs. -/
syntax program := ssa_instruction ("; " ssa_instruction)*

/--
`program!{x₁, x₂, …}( i₁; i₂; … )` elaborates the instructions `i₁`, `i₂`, etc
into a `Program`, assuming `x₁`, `x₂`, etc are valid free variables.
-/
syntax "program!" noWs "{" ident,* "}" noWs "(" optional(program) ")" : term

/--
`program!( i₁; i₂; … )` elaborates the instructions `i₁`, `i₂`, etc
into a *closed* `Program`, i.e., without free variables.
-/
macro "program!(" p:optional(program) ")" : term =>
  `(program!{}( $[$p:program]? ))

/--
`var!(n)` gives the variable with de Bruijn index `n`,
using `grind` to prove this index is valid.
-/
macro "var!(" n:term ")" : term => `(Var.ofFin ⟨$n, by grind⟩)

/-!
## Elaboration
--------------------------------------------------------------------------------
-/
open Lean.Elab (TermElabM)
open Qq

def InstructionElabM := StateT (List Lean.Ident) TermElabM

namespace InstructionElabM
instance : Monad InstructionElabM := by unfold InstructionElabM; infer_instance
instance : MonadLift TermElabM InstructionElabM := by unfold InstructionElabM; infer_instance
instance : MonadExceptOf Lean.Exception InstructionElabM := by unfold InstructionElabM; infer_instance
instance : Lean.MonadRef InstructionElabM := by unfold InstructionElabM; infer_instance
instance : MonadStateOf (List Lean.Ident) InstructionElabM := by unfold InstructionElabM; infer_instance

/--
Run an `x : InstructionElabM α` given a list of initial free variables `s`.
Returns the result of `x` as well as the list of free variables *after*
executing `x`. -/
def run (x : InstructionElabM α) (s : List Lean.Ident) : TermElabM (α × List Lean.Ident) :=
  StateT.run x s

/--
Trace the context of free variables.
FIXME: make this docstring better
-/
def traceContext (header : String := "context: ") : InstructionElabM Unit := do
  let ctx ← get
  trace[EffectSSA] "{header}{ctx}"

end InstructionElabM

/-- (Local) Syntax for `Vector α n` literals. -/
local syntax (name := «term!#[_,]») "!#[" withoutPosition(term,*,?) "]" : term
macro_rules
  | `(!#[ $elems,* ]) =>
      let n := Lean.quote elems.getElems.size
      `(Vector.mk (n:=$n) #[ $elems,* ] (by rfl))

open Lean in
def elabInstruction (τ : Q(Ty)) (i : Lean.TSyntax `ssa_instruction) :
     InstructionElabM (Q(Instruction $τ)) :=
  withRef i <| do
  trace[EffectSSA] "Elaborating instruction: {i}"
  InstructionElabM.traceContext "Context before elaboration:"
  match i with
  -- Basic memory ops with implicit effects
  | `(ssa_instruction| $x:ident := loadI[$t:term]($p:ident)) => do
        let t ← parseDType t
        let p : Var ← lookupVar p
        addVar x
        return q(.loadI $t $p)
  | `(ssa_instruction| storeI[$t:term]($p:ident, $x:ident)) => do
        let t ← parseDType t
        let p : Var ← lookupVar p
        let x : Var ← lookupVar x
        return q(.storeI $t $p $x)
  | `(ssa_instruction| allocI[$t:term]($p:ident)) => do
        let t ← parseDType t
        let p : Var ← lookupVar p
        return q(.allocI $t $p)
  | `(ssa_instruction| freeI[$t:term]($p:ident)) => do
        let t ← parseDType t
        let p : Var ← lookupVar p
        return q(.freeI $t $p)
  -- Basic memory ops in EffectSSA form
  | `(ssa_instruction| $e1:ident, $x:ident := loadE[$t:term]($e0:ident, $p:ident)) => do
        let t ← parseDType t
        let e0' : Var ← lookupVar e0
        let p : Var ← lookupVar p
        eraseVar e0
        addVar e1
        addVar x
        return q(.loadE $t $e0' $p)
  | `(ssa_instruction| $e1:ident := storeE[$t:term]($e0:ident, $p:ident, $x:ident)) => do
        let t ← parseDType t
        let e0' : Var ← lookupVar e0
        let p'  : Var ← lookupVar p
        let x' : Var ← lookupVar x
        eraseVar e0
        addVar e1
        return q(.storeE $t $e0' $p' $x')
  | `(ssa_instruction| $e1:ident := allocE[$t:term]($e0:ident, $p:ident)) => do
        let t ← parseDType t
        let e0' : Var ← lookupVar e0
        let p'  : Var ← lookupVar p
        eraseVar e0
        addVar e1
        return q(.allocE $t $e0' $p')
  | `(ssa_instruction| $e1:ident := freeE[$t:term]($e0:ident, $p:ident)) => do
        let t ← parseDType t
        let e0' : Var ← lookupVar e0
        let p'  : Var ← lookupVar p
        eraseVar e0
        addVar e1
        return q(.freeE $t $e0' $p')
  -- Effect Bookkeeping
  | `(ssa_instruction| $e1:ident, $e2:ident := split($e:ident)) => do
        let e' : Var ← lookupVar e
        eraseVar e
        addVar e1
        addVar e2
        return q(.split $e')
  | `(ssa_instruction| $e:ident := merge($e1:ident, $e2:ident)) => do
        let e1' : Var ← lookupVar e1
        let e2' : Var ← lookupVar e2
        eraseVar e1
        eraseVar e2
        addVar e
        return q(.merge $e1' $e2')
  | `(ssa_instruction| $e:ident := createEff) => do
        addVar e
        return q(@Instruction.createEff $τ)
  | `(ssa_instruction| consumeEff ( $e:ident )) => do
        let e' : Var ← lookupVar e
        eraseVar e
        return q(.consumeEff $e')
  | _ => Elab.throwUnsupportedSyntax
  where
    /--
    Parse a Lean term into a Lean expression of type `τ.DType`
    -/
    parseDType (t : Lean.Term) : TermElabM Q(($τ).DType) := withRef t <| do
      elabTermEnsuringTypeQ t q(($τ).DType)
    /-- Look up the index of a variable in the context. -/
    lookupVar (v : Lean.Ident) : InstructionElabM Var := do
      let ctx ← get
      ctx.idxOf? v |>.getDM (throwError "Unknown variable {v}")
    /--
    Add a new variable to the context.
    NOTE: This should generally be done *after* `lookupVar`, to ensure the
    latter gets the right bounds.
    -/
    addVar (v : Lean.Ident) : InstructionElabM Unit := do
      modify (v :: ·)
    /--
    Erase a (linear) variable from the context.
    NOTE: This should generally be done *after* `lookupVar`, to ensure the
    latter gets the right bounds.
    -/
    eraseVar (v : Lean.Ident) : InstructionElabM Unit := do
      modify (·.erase v)

macro_rules
  | `(program!{$_vs:ident,*}()) => `(Program.nil)

open Lean in
elab_rules : term
  | `(program!{$vs:ident,*}( $i:ssa_instruction $[; $is:ssa_instruction]* )) => do
      let τ ← mkFreshExprMVarQ q(Ty)
      let ⟨iExprs, ctx⟩ ← InstructionElabM.run (s := vs.getElems.toList) <|
        (#[i] ++ is).mapM (elabInstruction τ)
      trace[EffectSSA] "Final context: {ctx}"

      let cons := mkApp3 (mkConst ``Program.cons) τ
      return iExprs.foldr cons q(@Program.nil $τ)
