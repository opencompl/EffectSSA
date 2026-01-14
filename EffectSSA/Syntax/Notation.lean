import EffectSSA.Syntax.Basic

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
`program!( i₁; i₂; … )` elaborates into a *closed* `Program` with instructions
  `i₁`, `i₂`, etc.
-/
syntax "program!(" optional(program) ")" : term

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

--FIXME: generate a succinct docstring
def run (x : InstructionElabM α) : TermElabM α := do
  sorry

end InstructionElabM

/-- (Local) Syntax for `Vector α n` literals. -/
local syntax (name := «term!#[_,]») "!#[" withoutPosition(term,*,?) "]" : term
macro_rules
  | `(!#[ $elems,* ]) =>
      let n := Lean.quote elems.getElems.size
      `(Vector.mk (n:=$n) #[ $elems,* ] (by rfl))

open Lean in
def elabInstruction (τ : Q(Ty)) (i : Lean.TSyntax `ssa_instruction) :
     InstructionElabM (Σ (n : Nat), Q(Instruction $τ $n)) :=
  withRef i <| match i with
  | `(ssa_instruction| $x:ident := loadI[$t:term]($p:ident)) => do
        let t ← parseDType t
        let ⟨n, p⟩ ← lookupVar p
        addVar x
        return ⟨n, q(.loadI $t $p)⟩
  | `(ssa_instruction| storeI[$t:term]($p:ident, $x:ident)) => do
        let t ← parseDType t
        let ⟨n, vs⟩ ← lookupVars !#[p, x]
        let p : Var n := vs[0]
        let x : Var n := vs[1]
        return ⟨n, q(.storeI $t $p $x)⟩
  | `(ssa_instruction| allocI[$t:term]($p:ident)) => do
        let t ← parseDType t
        let ⟨n, p⟩ ← lookupVar p
        return ⟨n, q(.allocI $t $p)⟩
  | `(ssa_instruction| freeI[$t:term]($p:ident)) => do
        let t ← parseDType t
        let ⟨n, p⟩ ← lookupVar p
        return ⟨n, q(.freeI $t $p)⟩
  | `(ssa_instruction| $e1:ident, $x:ident := loadE[$t:term]($e0:ident, $p:ident)) => do
        let t ← parseDType t
        let ⟨n, vs⟩ ← lookupVars !#[e0, p]
        let e0' : Var n := vs[0]
        let p' : Var n := vs[1]
        eraseVar e0
        addVar e1
        addVar x
        return ⟨n, q(.loadE $t $e0' $p')⟩
  | `(ssa_instruction| $e1:ident := storeE[$t:term]($e0:ident, $p:ident, $x:ident)) => do
        let t ← parseDType t
        let ⟨n, vs⟩ ← lookupVars !#[e0, p, x]
        let e0' : Var n := vs[0]
        let p'  : Var n := vs[1]
        let x' : Var n := vs[2]
        eraseVar e0
        addVar e1
        return ⟨n, q(.storeE $t $e0' $p' $x')⟩
  | `(ssa_instruction| $e1:ident := allocE[$t:term]($e0:ident, $p:ident)) => do
        let t ← parseDType t
        let ⟨n, vs⟩ ← lookupVars !#[e0, p]
        let e0' : Var n := vs[0]
        let p'  : Var n := vs[1]
        eraseVar e0
        addVar e1
        return ⟨n, q(.allocE $t $e0' $p')⟩
  | `(ssa_instruction| $e1:ident := freeE[$t:term]($e0:ident, $p:ident)) => do
        let t ← parseDType t
        let ⟨n, vs⟩ ← lookupVars !#[e0, p]
        let e0' : Var n := vs[0]
        let p'  : Var n := vs[1]
        eraseVar e0
        addVar e1
        return ⟨n, q(.freeE $t $e0' $p')⟩
  | `(ssa_instruction| $e:ident := createEff) => do
        let n : Nat ← getVarBound
        addVar e
        return ⟨n, q(@Instruction.createEff $τ $n)⟩
  | `(ssa_instruction| consumeEff ( $e:ident )) => do
        let ⟨n, e'⟩ ← lookupVar e
        eraseVar e
        return ⟨n, q(.consumeEff $e')⟩
  | _ => Elab.throwUnsupportedSyntax
  where
    /--
    Parse a Lean term into a Lean expression of type `τ.DType`
    -/
    parseDType (t : Lean.Term) : TermElabM Q(($τ).DType) := withRef t <| do
      elabTermEnsuringTypeQ t q(($τ).DType)
    /--
    Look up the index of multiple variables in the context, statically showing
    that the returned variables all have the same (dynamic) bound `n` in their
    index, which corresponds to the number of variables in the current context.
    -/
    lookupVars {m} (vs : Vector Lean.Ident m) : InstructionElabM (Σ n, (Vector (Var n) m)) := do
      let ctx ← get
      let vs ← vs.mapM fun v =>
        ctx.findFinIdx? (· == v)
        |>.getDM (throwError "Unknown variable {v}")
      return ⟨ctx.length,  vs⟩
    /-- Look up the index of a single variable in the context. -/
    lookupVar (v : Lean.Ident) : InstructionElabM (Σ n, Var n) := do
      let ⟨n, vs⟩ ← lookupVars !#[v]
      return ⟨n, vs[0]⟩
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
    /-- Return the number of variables currently in the context. -/
    getVarBound : InstructionElabM Nat := do
      return (← get).length

def elabInstruction.asExpr (τ : Q(Ty)) (i : Lean.TSyntax `ssa_instruction) :
    InstructionElabM (Nat × Lean.Expr) := do
  let ⟨n, i⟩ ← elabInstruction τ i
  return (n, i)

macro_rules
  | `(program!()) => `(Program.nil)

open Lean in
elab_rules : term
  | `(program!( $i:ssa_instruction $[; $is:ssa_instruction]* )) => do
      let τ ← mkFreshExprMVarQ q(Ty)
      let is := is.push i
      let iExprs ← InstructionElabM.run <|
        is.mapM (elabInstruction.asExpr τ)

      let n0 : Nat := (iExprs.back?.map Prod.fst).getD 0
      let nil := q(@Program.nil $τ $n0)
      let mkProgram := fun (n, i) =>
        mkApp4 (mkConst ``Program.cons) τ (toExpr n) i
      return iExprs.foldr mkProgram nil
