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
  | freeI (p : Var n)
  -- Basic memory ops in EffectSSA form
  | loadE (t : τ.DType) (eff : Var n) (p : Var n)
  | storeE (t : τ.DType) (eff : Var n) (p : Var n) (x : Var n)
  | allocE (t : τ.DType) (eff : Var n) (p : Var n)
  | freeE (eff : Var n) (p : Var n)
  -- FIXME: the draft also has stack address & constant value instruction
  -- Effect Bookkeeping
  | createEff
  | consumeEff (e : Var n)

/--
`i.results` returns the number of new variables bound by instruction `i`,
minus the number of *linear* variables consumed by `i`.
-/
def Instruction.netResults : Instruction τ n → Int
  | loadI .. => 1
  | storeI .. => 0
  | allocI .. => 0
  | freeI .. => 0
  | loadE .. => 1
  | storeE .. => 0
  | allocE .. => 0
  | freeE .. => 0
  | createEff => 1
  | consumeEff .. => -1

inductive Program (τ : Ty) : Nat → Type where
  | nil : Program τ n
  | cons : (i : Instruction τ n) → Program τ (n + i.netResults).toNat → Program τ n

/-
FIXME: I wonder if I'm not getting the worst of both worlds by doing intrinsically
tracked de Bruijn indices but extrinsically typed. To track the indices, `Program`
has become a custom inductive, instead of just a `List`, so I'm going to have to
implement a bunch of API for it anyway.
-/
