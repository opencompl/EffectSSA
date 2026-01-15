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
inductive Instruction (τ : Ty) (n : Nat) where
  -- Basic memory ops with implicit effects
  | loadI (t : τ.DType) (p : Var n)
  | storeI (t : τ.DType) (p : Var n) (x : Var n)
  | allocI (t : τ.DType) (p : Var n)
  | freeI (t : τ.DType) (p : Var n)
  -- Basic memory ops in EffectSSA form
  | loadE (t : τ.DType) (eff : Var n) (p : Var n)
  | storeE (t : τ.DType) (eff : Var n) (p : Var n) (x : Var n)
  | allocE (t : τ.DType) (eff : Var n) (p : Var n)
  | freeE (t : τ.DType) (eff : Var n) (p : Var n)
  -- FIXME: the draft also has stack address & constant value instruction
  -- Effect Bookkeeping
  | split (eff : Var n)
  | merge (eff₁ : Var n) (eff₂ : Var n)
  | createEff
  | consumeEff (e : Var n)

/--
`i.results` gives the number of (live) free variables available after executing
an instruction `i`, taking into account free variables available to `i`.

Here, live means that any linear variables consumed by `i` are excluded.
-/
def Instruction.results : Instruction τ n → Nat
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
A program is a (possibly empty) sequence of instructions.
It is thus morally similar to a `List (Instruction ..)`, except that `Program`
additionally tracks the bound on free variables available to each instruction.

Programs grow upwards, such that `cons i p` represents `i ; p`,
first executing instruction `i` and then the rest of the program `p`.
-/
inductive Program (τ : Ty) : Nat → Type where
  | nil : Program τ n
  | cons : (i : Instruction τ n) → Program τ i.results → Program τ n

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

/--
`p.results` gives the number of *live* free variables available after executing
program `p`.

Here, live means that any linear variables that have already been
consumed during the execution of `p` are explicitly excluded.
-/
def Program.results : Program τ n → Nat
  | nil => n
  | cons _ p => results p

/--
`i ;> p` is the preferred spelling for adding an instruction to the
front of a program.
-/
infixl:67 " ;> " => Program.cons

/--
`p.append q` concatenates two programs.

NOTE: we cannot use standard `++` notation for this, as the type of `q`
depends on `p`.
-/
def Program.append : (p : Program τ n) → Program τ p.results → Program τ n
  | .nil, q => q
  | i ;> p, q => i ;> (p.append q)
