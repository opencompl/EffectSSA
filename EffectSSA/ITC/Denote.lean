import EffectSSA.ITC.CanonicalEventTree

/-!
# Denotation of ITCs
-/
namespace EffectSSA.ITC

/-!
## Domain
-/

/--
The domain of ITC denotations; rational numbers in the interval `[0,1)`.
-/
structure FRat : Type where
  val  : Rat
  zero_le : 0 ≤ val := by grind
  lt_one  : val < 1 := by grind

namespace FRat

attribute [grind! . ] FRat.zero_le FRat.lt_one

@[grind] def left (x : FRat) (h : x.val < 0.5 := by grind) : FRat where
  val := 2*x.val

@[grind] def right (x : FRat) (h : x.val ≥ 0.5 := by grind) : FRat where
  val := 2*x.val - 1

/--
Split maps a rational `x` to either `2x` or `2x - 1`, depending on which of the
two are in the interval (i.e., depending on whether `x < 0.5`).
-/
@[grind] def splitRec (l : FRat → α) (r : FRat → α) : FRat → α := fun x =>
  if hx : x.val < 0.5 then
    l x.left
  else
    r x.right

section SplitLemmas
variable (x : FRat)

end SplitLemmas
end FRat

/-!
## EventTree
An EventTree represent a function `FRat → Nat`.
-/
namespace EventTree

/--
`denote` interprets an EventTree as a function `FRat → Nat`.
-/
def denote : EventTree → FRat → Nat
  | .leaf n, _ => n
  | .node n l r, x =>
    n + x.splitRec l.denote r.denote

section DenoteLemmas
variable {e : EventTree} {l r : EventTree} {n : Nat} {x : FRat}

attribute [local grind] denote

@[simp, grind =] theorem denote_leaf : (leaf n).denote x = n := by rfl
@[simp, grind =] theorem denote_node : (node n l r).denote x = n + x.splitRec (l.denote ·) (r.denote ·) := by rfl

@[simp, grind =] theorem denote_node_left (hx : x.val < 0.5) :
    (node n l r).denote x = n + l.denote x.left := by grind
@[simp, grind =] theorem denote_node_right (hx : x.val ≥ 0.5) :
    (node n l r).denote x = n + r.denote x.right := by grind

@[simp, grind =] theorem denote_sink : (e.sink k hk).denote x = e.denote x - k := by
  cases e <;> grind
@[simp, grind =] theorem denote_lift : (e.lift k).denote x = e.denote x + k := by
  cases e <;> grind

@[simp, grind! .] theorem rootValue_le_denote : e.rootValue ≤ e.denote x := by
  cases e <;> grind
@[simp, grind .] theorem minValue_le_denote : e.minValue ≤ e.denote x := by
  induction e generalizing x <;> grind
@[simp, grind .] theorem denote_le_maxValue : e.denote x ≤ e.maxValue := by
  induction e generalizing x <;> grind


@[simp, grind =]
theorem denote_normalize : e.normalize.denote = e.denote := by
  funext x; induction e generalizing x <;> grind

end DenoteLemmas
end EventTree

@[simp, grind] abbrev CanonicalEventTree.denote (e : CanonicalEventTree) : FRat → Nat := e.raw.denote


end EffectSSA.ITC
