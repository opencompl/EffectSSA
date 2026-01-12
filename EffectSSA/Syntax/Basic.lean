import EffectSSA.Assumptions.MemorySignature

/-!
# Program Syntax

This file sets up an *untyped* syntax of instructions and programs.

The syntax uses de Bruijn indices, so we do track an upper bound on the number
of free variables for convenience.

-/
namespace EffectSSA

/--
`Var n` is a de Bruijn index representing a variable, given an upper bound `n`
on the number of available variables.
-/
def Var n := Fin n

/--
`Instruction τ` represents a single instruction (including arguments).
-/
inductive Instruction (τ : Ty) where
  -- Basic memory ops with implicit effects
  | loadI (p : Var n)
  | storeI (t : τ.DType) (p : Var n) (x : Var n)
  | allocI (t : τ.DType) (p : Var n)
  | freeI (p : Var n)
  -- Basic memory ops in EffectSSA form
  | loadE (eff : Var n) (p : Var n)
  | storeE (t : τ.DType) (eff : Var n) (p : Var n) (x : Var n)
  | allocE (t : τ.DType) (eff : Var n) (p : Var n)
  | freeE (eff : Var n) (p : Var n)
  -- FIXME: the draft also has stack address & constant value instruction

/--
`i.results` returns the number of new variables bound by instruction `i`.
-/
def Instruction.results : Instruction τ → Nat
  | loadI .. => 1
  | storeI .. => 0
  | allocI .. => 0
  | freeI .. => 0
  | loadE .. => 2
  | storeE .. => 1
  | allocE .. => 1
  | freeE .. => 1

inductive Program (τ : Ty) : Nat → Type where
  | nil : Program τ n
  | cons : (i : Instruction τ) → Program τ n

/-
FIXME: I wonder if I'm not getting the worst of both worlds by doing intrinsically
tracked de Bruijn indices but extrinsically typed. To track the indices, `Program`
has become a custom inductive, instead of just a `List`, so I'm going to have to
implement a bunch of API for it anyway.
-/
