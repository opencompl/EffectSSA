import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Syntax.Untyped.Var

/-!
# Program Syntax

This file sets up an *untyped* syntax of instructions and programs.

The syntax uses de Bruijn indices, so we do track an upper bound on the number
of free variables for convenience.

-/
namespace EffectSSA

/-!
## Types
--------------------------------------------------------------------------------
-/

/--
`Instruction τ` represents a single instruction (including arguments).
-/
inductive Instruction (τ : Ty) where
  -- Basic memory ops with implicit effects
  | loadI (t : τ.DType) (p : Var)
  | storeI (t : τ.DType) (p : Var) (x : Var)
  | allocI (t : τ.DType) (p : Var)
  | freeI (t : τ.DType) (p : Var)
  -- Basic memory ops in EffectSSA form
  | loadE (t : τ.DType) (eff : Var) (p : Var)
  | storeE (t : τ.DType) (eff : Var) (p : Var) (x : Var)
  | allocE (t : τ.DType) (eff : Var) (p : Var)
  | freeE (t : τ.DType) (eff : Var) (p : Var)
  -- FIXME: the draft also has stack address & constant value instruction
  -- Effect Bookkeeping
  | split (eff : Var)
  | merge (eff₁ : Var) (eff₂ : Var)
  | createEff
  | consumeEff (e : Var)

/--
`InstructionSeq` is a (possibly empty) sequence of instructions.
It is thus equivalent to a `List (Instruction ..)`, although we deliberately
don't model it as such to retain a simple recursion principle.

Programs grow upwards, such that `cons i p` represents first executing
instruction `i` before the rest of the program `p`.
-/
inductive InstructionSeq (τ : Ty) : Type where
  | nil : InstructionSeq τ
  | cons : Instruction τ → InstructionSeq τ → InstructionSeq τ
  -- toList : List (Instruction τ)

/--
A `Program` is a sequence of instructions (`InstructionSeq`) together with
designated return variables.
-/
@[grind cases]
structure Program (τ : Ty) where
  instructions : InstructionSeq τ
  returnVars : List Var

/-!
## Definitions
--------------------------------------------------------------------------------
-/
section Defs
namespace InstructionSeq

/-! ### Pseudo-constructors -/
/--
`i ;> p` is the preferred spelling for adding an instruction to the
front of a program.
-/
infixl:67 " ;> " => InstructionSeq.cons

def toList : InstructionSeq τ → List (Instruction τ)
  | .nil => []
  | i ;> p => i :: p.toList

def ofList : List (Instruction τ) → InstructionSeq τ
  | [] => .nil
  | i :: p => i ;> ofList p

/-! ### Folds -/

@[inherit_doc List.foldl]
def foldl (f : α → Instruction τ → α) (init : α) (p : InstructionSeq τ) :=
  p.toList.foldl f init

@[inherit_doc List.foldlM]
def foldlM [Monad m] (f : α → Instruction τ → m α) (init : α) (p : InstructionSeq τ) :=
  p.toList.foldlM f init

/-! ### Append -/

/--
`p ++ q` concatenates two instruction sequences.
-/
def append : InstructionSeq τ → InstructionSeq τ → InstructionSeq τ
  | nil, q => q
  | i ;> p, q => i ;> (p.append q)
instance : Append (InstructionSeq τ) where append := InstructionSeq.append

end InstructionSeq
