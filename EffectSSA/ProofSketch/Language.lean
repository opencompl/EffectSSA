module

public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.VarSet

/-!
# Language Typeclass

-/
public section
namespace EffectSSA.ProofSketch

/-!
## Environment
We start by setting up the notion of the environment in which instructions will
be denoted.
-/
section Env

/--
`PreLanguage` is an intermediate class in the construction of `Language`,
with all the prerequites needed to define environments.

Downstream users should *always* use `Language` directly.
-/
class PreLanguage (ι : Type) (Var Val State : outParam Type) where
  /-- The initial (global) state that execution of a program starts with. -/
  initialState : State

/--
An environment `ρ : Env ι` bundles a map from variables to values, with a global state.
-/
structure Env (ι) {Var Val State} [PreLanguage ι Var Val State] where
  /-- A partial map from variables (i.e, virtual registers) to values. -/
  regs : Var → Option Val := fun _ => none
  /-- The global state, e.g, for memory and UB -/
  state : State := PreLanguage.initialState ι
  /--
  Whether an interpreter error occured (e.g, a reference to an undefined
  variable). This should never happen in well-formed programs.
  -/
  error : Bool := false

end Env

/-! ## Language Class -/
/--
`Language` bundles the basic assumptions that form a language in our setting:

* `ι` is the type of instructions
* `Var` is the type variable names
* `Val` is the type of runtime values
* `State` is the type of global state (e.g, memory)

Besides these types, we ask for:

* An initial global state,
* A way to denote individual instructions as a map on (stateful) environments,
* That equality of instructions is decidable,
* A map from an instruction to its arguments, and
* A map from an instruction to its results
-/
class Language (ι : Type) (Var Val State : outParam Type) extends
    PreLanguage ι Var Val State,
    Denote ι (Env ι → Env ι) where

  /-- Equality of instructions must be decidable. -/
  [decideInstEq : DecidableEq ι]

  /-- `iArgs i` is the set of arguments of instruction `i`. -/
  iArgs : ι → VarSet Var
  /-- `iResults i` is the set of results of instruction `i`. -/
  iResults : ι → VarSet Var

attribute [reducible, instance] Language.decideInstEq
