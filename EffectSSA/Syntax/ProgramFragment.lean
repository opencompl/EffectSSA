import EffectSSA.Syntax.Basic

/-!
# Program Fragments

This file defines program fragments, which are essentially open programs with
designated return variables. These will be used to represent rewrites, and in
particular, the designated variables will be significant when defining
equivalence of program fragments.
-/
namespace EffectSSA

/-!
## `ProgramFragment` type
--------------------------------------------------------------------------------
-/

/--
A program fragment is simply a program with some designated return variables
at the end of said program.
-/
structure ProgramFragment (τ) (n : Nat) where
  program : Program τ n
  returnVars : List (Var program.results)

/-!
## Definitions
--------------------------------------------------------------------------------
-/
namespace ProgramFragment
variable {τ} {n} (f : ProgramFragment τ n)

abbrev internalResults : Nat := f.program.results
abbrev externalResults : Nat := f.returnVars.length
