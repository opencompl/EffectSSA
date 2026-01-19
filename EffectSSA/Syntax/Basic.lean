import EffectSSA.Assumptions.MemorySignature
import EffectSSA.Syntax.Var

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
A program is a (possibly empty) sequence of instructions.
It is thus morally similar to a `List (Instruction ..)`, except that `Program`
additionally tracks the bound on free variables available to each instruction.

Programs grow upwards, such that `cons i p` represents `i ; p`,
first executing instruction `i` and then the rest of the program `p`.
-/
inductive Program (τ : Ty) : Type where
  | nil : Program τ
  | cons : Instruction τ → Program τ → Program τ
  -- toList : List (Instruction τ)

/-
FIXME: I wonder if I'm not getting the worst of both worlds by doing intrinsically
tracked de Bruijn indices but extrinsically typed. To track the indices, `Program`
has become a custom inductive, instead of just a `List`, so I'm going to have to
implement a bunch of API for it anyway.
-/

/-!
## Definitions
--------------------------------------------------------------------------------
-/
section Defs
namespace Program

/-! ### Pseudo-constructors -/
/--
`i ;> p` is the preferred spelling for adding an instruction to the
front of a program.
-/
infixl:67 " ;> " => Program.cons

def toList : Program τ → List (Instruction τ)
  | .nil => []
  | i ;> p => i :: p.toList

def ofList : List (Instruction τ) → Program τ
  | [] => .nil
  | i :: p => i ;> ofList p

/-! ### Folds -/

@[inherit_doc List.foldl]
def foldl (f : α → Instruction τ → α) (init : α) (p : Program τ) :=
  p.toList.foldl f init

@[inherit_doc List.foldlM]
def foldlM [Monad m] (f : α → Instruction τ → m α) (init : α) (p : Program τ) :=
  p.toList.foldlM f init

end Program


/-! ### Resulting variables -/

/--
`i.results n` gives the number of (live) free variables available after executing
an instruction `i`, assuming `i` has access to `n` free variables.

Here, live means that any linear variables consumed by `i` are excluded.
-/
@[grind =]
def Instruction.results (n : Nat) : Instruction τ → Nat
  | loadI .. => n + 1
  | storeI .. => n
  | allocI .. => n
  | freeI .. => n
  | loadE .. => n + 1
  | storeE .. => n
  | allocE .. => n
  | freeE .. => n
  | split .. => n + 1
  | merge .. => n - 1
  | createEff => n + 1
  | consumeEff .. => n - 1

/--
`p.results n` gives the number of *live* free variables available after executing
program `p`, assuming `p` has access to `n` free variables.

Here, live means that any linear variables that have already been
consumed during the execution of `p` are explicitly excluded.
-/
def Program.results (n : Nat) (p : Program τ) : Nat :=
  p.foldl Instruction.results n

/--
`p ++ q` concatenates two programs.
-/
def Program.append : Program τ → Program τ → Program τ
  | nil, q => q
  | i ;> p, q => i ;> (p.append q)
instance : Append (Program τ) where append := Program.append
