import EffectSSA.Syntax
import EffectSSA.Semantics
import EffectSSA.Types

/-!
# Rewrite data structure
-/
namespace EffectSSA

/-!
## Data Structures
--------------------------------------------------------------------------------
-/

/--
A program fragment is simply a program with some designated return variables
at the end of said program.
-/
structure ProgramFragment τ where
  program : Program τ
  returnVars : List Var

/--
A rewrite consists of two program fragments.
-/
structure Rewrite τ where
  src : ProgramFragment τ
  tgt : ProgramFragment τ

/-!
## Structural Lemmas
--------------------------------------------------------------------------------
-/

@[simp /-, grind = -/]
theorem ProgramFragment.program_mk : (mk p vs).program = p := rfl

/-!
## Wellformedness Constraints
--------------------------------------------------------------------------------
-/

/--
A program fragment is welltyped, for a given set of return types, when
(a) the program is welltyped, producing an output context `Δ`, and
(b) each return variable is assigned the expected return type in `Δ`.
-/
@[grind =]
def ProgramFragment.WellTyped (Γ : Context τ) (p : ProgramFragment τ)
    (returnTypes : List τ.Typ) : Prop :=
  ∃ (Δ : Context τ),
    Program.WellTypedWith Γ p.program Δ ∧ Δ.isUnrestricted
    ∧ (∀ (i : Fin p.returnVars.length), Δ[p.returnVars[i]]? = returnTypes[i]?)

open ProgramFragment (WellTyped) in
/--
A rewrite is wellformed, if both fragments are welltyped, under the same context
and with the same expected return types.
-/
@[grind =]
def Rewrite.WellFormed (Γ : Context τ) (r : Rewrite τ) : Prop :=
  ∃ ts, WellTyped Γ r.src ts ∧ WellTyped Γ r.tgt ts

/-! ### Welltypedness of a `ProgramFragment` is decidable -/
instance (p : ProgramFragment τ) : Decidable (p.WellTyped Γ ts) :=
  match p.program.typeCheck Γ with
  | .isFalse h => .isFalse <| by grind
  | .isTrue Δ h₁ h₂ =>
      if h : ∀ (i : Fin p.returnVars.length), Δ[p.returnVars[i]]? = ts[i]? then
        .isTrue (by grind)
      else
        .isFalse (by grind)

/-!
## Semantics Correctness Constraints
--------------------------------------------------------------------------------
-/
variable {τ} [MemoryModel τ]

open Semantics in
/--
Execute all instructions in a program fragment sequentially,
but return only the values computed for the designated return variables.
-/
def ProgramFragment.exec (env : Environment τ) (p : ProgramFragment τ) :
    ExecM τ (List τ.Val) := do
  let env ← p.program.exec env
  p.returnVars.mapM env.get

/--
A rewrite is correct, if the source and target fragments compute the same values
for the return variables (given the same environment).
-/
def Rewrite.Correct (r : Rewrite τ) : Prop :=
  -- FIXME: this is actually too granular, as it looks for strict equality of
  --        of traces, whereas we want to consider something a bit looser, e.g.
  --        to disregard the specific order of load events.
  ∀ {env} {Γ}, env.WellTyped Γ → r.src.exec env = r.tgt.exec env
