import EffectSSA.Types.Basic

/-!
# Basic Lemmas about Types
-/
namespace EffectSSA
variable {τ : Ty}

namespace Ty.Typ

@[grind =] theorem isUnrestricted_iff (t : τ.Typ) : t.isUnrestricted = decide (t ≠ .eff) := by
  grind [Typ.isUnrestricted]

@[simp, grind =] theorem isUnrestricted_data (d : τ.DType) : (data d).isUnrestricted := by grind
@[simp, grind =] theorem isUnrestricted_ptr : (ptr : τ.Typ).isUnrestricted := by grind
@[simp, grind =] theorem isUnrestricted_eff : (eff : τ.Typ).isUnrestricted = false := by grind
