module

public import ITreeExtras
public import ITreeExtras.Basic

/-!
# ITree `HasEffect` and `MayReturn` Predicates

`HasEffect` and `MayReturn` are now provided as inductive predicates by
`ITreeExtras.HasEffect`. This file provides additional lemmas.
-/

@[expose] public section
namespace ITree.ITree
variable {ε : Type} {κ : ε → Type} [Effect ε κ] {α : Type _}

/-! ## Lemmas -/
section Lemmas
attribute [grind =] unfold_ret unfold_vis unfold_tau

/-! ### HasEffect -/


/-! ### MayReturn -/


end Lemmas
end ITree.ITree
