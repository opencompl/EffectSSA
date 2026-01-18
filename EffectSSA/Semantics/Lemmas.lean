import EffectSSA.Syntax
import EffectSSA.Semantics.Program

/-!
# Lemmas about semantics
-/
namespace EffectSSA
variable {τ} [MemoryModel τ]

/-
The following theorem does not quite work, because the `.results` are not
nicely def-eq.
-/
-- theorem Program.exec_append (p : Program τ) (q : Program τ) :
--     (p.append q).exec =
--       have h := sorry
--       fun env => (p.exec env >>= (q.cast h).exec) := by
--   sorry
