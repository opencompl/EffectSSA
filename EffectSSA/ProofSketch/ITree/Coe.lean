module

public import ITree

/-!
# Subeffect Coercion
-/
@[expose] public section
namespace ITree
namespace Effect

instance instCoeTOfSubeffect {ε δ} [ε -< δ] {e} : CoeT ε.I e δ.I where
  coe := (Subeffect.map e).1
