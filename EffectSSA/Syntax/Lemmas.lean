import EffectSSA.Syntax.Basic

/-!
# Syntax lemmas
-/
namespace EffectSSA
variable {τ : Ty} -- [MemorySignature τ]

/-!
## Casting
--------------------------------------------------------------------------------
-/

/--
Change the bound of an instruction to a provably equal bound.
-/
def Instruction.cast (h : n = m) : Instruction τ n → Instruction τ m
  -- TODO: generate this function
  | _ => sorry

@[simp]
theorem Instruction.results_cast (h : n = m) (i : Instruction τ n) :
    (i.cast h).results = i.results := by
  sorry

/--
Change the bound of a program to a provably equal bound.
-/
def Program.cast (h : n = m) : Program τ n → Program τ m
  | .nil => .nil
  | i ;> p => (i.cast h) ;> (p.cast <| by simp)

/-!
## Program Lemmas
--------------------------------------------------------------------------------
-/
namespace Program

/-! ### `results` -/

@[simp, grind =]
theorem results_nil (n : Nat) :
    (.nil : Program τ n).results = n := by
  rfl

@[simp, grind =]
theorem results_cons {i : Instruction τ n} {p : Program τ i.results} :
    (i ;> p).results = p.results := by
  simp [results]

@[simp, grind =]
theorem results_append {p : Program τ n} {q : Program τ p.results} :
    (p.append q).results = q.results := by
  induction p <;> simp_all [append]

@[simp, grind =]
theorem results_cast (h : n = m) (p : Program τ n) :
    (p.cast h).results = p.results := by
  induction p generalizing m <;> simp_all [cast]

end Program
