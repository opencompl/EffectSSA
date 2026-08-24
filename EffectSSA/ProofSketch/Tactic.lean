module

public section

/-!
## List.idxOf? Simplification

We register two simp-lemmas for the pattern:
  `List.idxOf? x [y, z, ...] = some $n`
Where the rhs is a constant
-/
section ListIdxOf

/-- Peel off a matching head. -/
@[simp, grind =]
theorem List.idxOf?_cons_eq_some_zero [BEq α] [LawfulBEq α] {a b : α} {xs : List α} :
    (b :: xs).idxOf? a = some 0 ↔ b = a := by
  simp [List.idxOf?_cons]

/-- Peel off a non-matching head. -/
@[simp, grind =]
theorem List.idxOf?_cons_eq_some_succ [BEq α] [LawfulBEq α] {a b : α} {xs : List α} {n : Nat} :
    (b :: xs).idxOf? a = some (n + 1) ↔ b ≠ a ∧ xs.idxOf? a = some n := by
  simp only [idxOf?_cons, beq_iff_eq, ne_eq]
  split <;> (simp; grind)

end ListIdxOf
