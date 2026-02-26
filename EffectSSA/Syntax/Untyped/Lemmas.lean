import EffectSSA.Syntax.Untyped.Basic

/-!
# Syntax lemmas
-/
namespace EffectSSA
variable {τ : Ty} -- [MemorySignature τ]

/-!
## InstructionSeq Lemmas
--------------------------------------------------------------------------------
-/
namespace InstructionSeq
variable {i : Instruction τ} {p q : InstructionSeq τ}

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

/-! ### foldlM -/

@[simp, grind =] theorem foldlM_nil [Monad m] (f : α → Instruction τ → m α) (init : α) :
    foldlM f init (@nil τ) = pure init := by rfl

@[simp, grind =] theorem foldlM_cons [Monad m] (f : α → Instruction τ → m α) (init : α) :
    foldlM f init (i ;> p) = f init i >>= fun a => foldlM f a p := by rfl

end InstructionSeq
