module

public import EffectSSA.ProofSketch.Pattern
public import Lean.Elab.Tactic.Simp

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

/-!
## `Pattern` `getElem` Reduction

Simproc that reduces `(P : Pattern _ _)[k]` to a spelled-out chain of
`List.cons` / `InstSeq.cons` applications, whenever the index `k` is a concrete
natural number literal and the reduction succeeds under default transparency.
-/
section PatternGetElem

open Lean Meta Simp

namespace EffectSSA.ProofSketch

/--
Assuming that `e` is already in whnf, recursively reduce the rest of the spine
of the list (leaving each `cons`-head untouched).

`u` has to be be such that `e` is of type `List α` for some `α : Type u`;
this is passed in rather than re-computed since it remains constant for the
whole list.
-/
private meta partial def reduceInstSeqSpine (u : Level) (e : Expr) : MetaM Expr := do
  match_expr e with
  | List.cons α head tail =>
      let tail ← whnf tail
      let tail ← reduceInstSeqSpine u tail
      return mkApp3 (mkConst ``List.cons [u]) α head tail
  | _ => return e

/--
`dsimp`-procedure that rewrites `(P : Pattern _ _)[k]` — with `k` a concrete
`Nat` literal — into a spelled-out chain of `List.cons` / `InstSeq.cons`
applications, using default transparency.

If the initial reduction does not produce a `List.cons` or `List.nil`, the
expression is left untouched.  When it succeeds, the rest of the sequence is
reduced recursively, but each individual instruction (the `cons`-heads) is
left as-is.
-/
dsimproc reducePatternGetElem
    (@GetElem.getElem (EffectSSA.ProofSketch.Pattern _ _) Nat _ _ _ _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ _ idx _ ← e | return .continue
  let some _ ← getNatValue? idx | return .continue
  let e ← withDefault <| whnf e
  match_expr e with
  | List.cons α _ _ =>
      let u ← getDecLevel α
      let e ← withDefault <| reduceInstSeqSpine u e
      return .done <| e
  | List.nil _ => return .done e
  | _ => return .continue

end EffectSSA.ProofSketch

end PatternGetElem
