import EffectSSA.Semantics.Program

/-!
# `ProgramFragment` semantics
-/
namespace EffectSSA
open Semantics
variable (τ : Ty) [MemoryModel τ]

/--
Execute all instructions in a program fragment sequentially,
but return only the values computed for the designated return variables.
-/
def ProgramFragment.exec (env : Environment τ n) (p : ProgramFragment τ n) :
    ExecM τ (Environment τ p.externalResults) := do
  let env ← p.program.exec env
  let vars : List.Vector .. := ⟨p.returnVars, rfl⟩
  let vals := vars.map env.get
  return .ofVector vals
