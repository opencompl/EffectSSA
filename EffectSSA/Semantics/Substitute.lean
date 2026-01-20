import EffectSSA.Syntax
import EffectSSA.Semantics.Program
import EffectSSA.Semantics.Lemmas

/-!
# Semantics of Substitution
-/
namespace EffectSSA
variable {τ} [MemoryModel τ]

namespace Semantics.Environment

def map (σ : Substitution) : Environment τ → Environment τ :=
  sorry

end Semantics.Environment

namespace Program

theorem exec_substitute (p : Program τ) :
    (p.substitute σ).exec env = p.exec (env.map σ) := by
  induction p
  case nil => simp [exec_nil]
