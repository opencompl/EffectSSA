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
A rewrite consists of two program fragments.
-/
structure Rewrite τ where
  rSrc : Program τ
  rTgt : Program τ

/--
A rewrite is wellformed, if both fragments are welltyped, under the same context
and with the same expected return types.
-/
structure TRewrite (Γ : Context τ) (ts : List τ.Typ) extends raw : Rewrite τ where
  wt_src : raw.rSrc.WellTyped Γ ts := by typecheck
  wt_tgt : raw.rTgt.WellTyped Γ ts := by typecheck

/-!
## Semantics Correctness Constraints
--------------------------------------------------------------------------------
-/
variable {τ} [LawfulMemoryModel τ] {Γ : Context τ}

grind_pattern TRewrite.wt_src => (TRewrite.raw self).rSrc
grind_pattern TRewrite.wt_tgt => (TRewrite.raw self).rTgt

def TRewrite.src (rw : TRewrite Γ ts) : TProgram Γ ts where
  program := rw.raw.rSrc
def TRewrite.tgt (rw : TRewrite Γ ts) : TProgram Γ ts where
  program := rw.raw.rTgt

/--
A rewrite is correct, if the source and target fragments are equivalent.
-/
@[grind] def TRewrite.Correct (r : TRewrite Γ ts) : Prop :=
  r.src ≈ r.tgt
