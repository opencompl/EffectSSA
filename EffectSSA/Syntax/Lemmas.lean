import EffectSSA.Syntax.Basic

/-!
# Syntax lemmas
-/
namespace EffectSSA
variable {τ : Ty} -- [MemorySignature τ]

/-!
## Program Lemmas
--------------------------------------------------------------------------------
-/
namespace Program
variable {i : Instruction τ} {p q : Program τ}

/-! ### toList -/

@[simp, grind =] theorem toList_nil : (@nil τ).toList = [] := rfl
@[simp, grind =] theorem toList_cons : (i ;> p).toList = i :: p.toList := rfl

theorem toList_inj : p.toList = q.toList ↔ p = q := by
  induction p generalizing q <;> cases q <;> grind

/-! ### mk -/

@[simp, grind =] theorem ofList_nil : @ofList τ [] = nil := rfl
@[simp, grind =] theorem ofList_cons : ofList (i :: is) = i ;> ofList is := rfl

/-! ### append -/

@[simp, grind =] theorem append_eq : p.append q = p ++ q := rfl

@[simp, grind =] theorem nil_append : nil ++ p = p := rfl
@[simp, grind =] theorem cons_append : (cons i p) ++ q = cons i (p ++ q) := rfl

@[simp, grind =] theorem append_nil : p ++ nil = p := by
  induction p <;> grind

@[simp, grind =]
theorem toList_append : (p ++ q).toList = p.toList ++ q.toList := by
  induction p generalizing q <;> cases q <;> grind

/-! ### `results` -/

@[simp, grind =]
theorem results_nil (n : Nat) :
    (.nil : Program τ).results n = n := rfl

@[simp, grind =]
theorem results_cons {i : Instruction τ} {p : Program τ} :
    (i ;> p).results n = p.results (i.results n) := rfl

@[simp, grind =]
theorem results_append {p q : Program τ} :
    (p ++ q).results n = q.results (p.results n) := by
  induction p generalizing n <;> grind

end Program
