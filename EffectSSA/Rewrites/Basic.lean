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
  src : Program τ
  tgt : Program τ

/--
A rewrite is wellformed, if both fragments are welltyped, under the same context
and with the same expected return types.
-/
structure TRewrite (Γ : Context τ) (ts : List τ.Typ) where
  raw : Rewrite τ
  wt_src : raw.src.WellTyped Γ ts
  wt_tgt : raw.tgt.WellTyped Γ ts

/-!
## Semantics Correctness Constraints
--------------------------------------------------------------------------------
-/
variable {τ} [MemoryModel τ] {Γ : Context τ}

grind_pattern TRewrite.wt_src => (TRewrite.raw self).src
grind_pattern TRewrite.wt_tgt => (TRewrite.raw self).tgt

def TRewrite.src (rw : TRewrite Γ ts) : TProgram Γ ts where
  program := rw.raw.src
def TRewrite.tgt (rw : TRewrite Γ ts) : TProgram Γ ts where
  program := rw.raw.tgt

/--
A rewrite is correct, if the source and target fragments are equivalent.
-/
@[grind] def TRewrite.Correct (r : TRewrite Γ ts) : Prop :=
  r.src ≈ r.tgt
