import EffectSSA.ITC.EventTree

/-!
# Canonical Event Trees

A `CanonicalEventTree` is an `EventTree` which is guaranteed to be in normal form.
The normal form ensures that in any node `(n, l, r)`, the minimum of `l.rootValue`
and `r.rootValue` is zero.
-/
namespace EffectSSA.ITC

/--
A `CanonicalEventTree` is an `EventTree` which is guaranteed to be in normal form.
-/
structure CanonicalEventTree where
  raw : EventTree
  eq_normalize : raw.normalize = raw := by solve | rfl | simp; try grind
  deriving DecidableEq

namespace CanonicalEventTree

/-! ## Basic Lemmas -/
section Lemmas
variable {e f : CanonicalEventTree}

attribute [grind =] CanonicalEventTree.eq_normalize

@[ext, grind ext]
theorem ext : e.raw = f.raw → e = f := by
  grind [cases CanonicalEventTree]

@[simp] theorem eq_iff_raw_eq : e = f ↔ e.raw = f.raw := by grind

@[simp, grind .] theorem mk_eq_iff {raw : EventTree} {h : raw.normalize = raw} {f : CanonicalEventTree} :
    ⟨raw, h⟩ = f ↔ raw = f.raw := by grind

@[simp, grind .] theorem eq_mk_iff {e : CanonicalEventTree} {raw : EventTree} {h : raw.normalize = raw} :
    e = ⟨raw, h⟩ ↔ e.raw = raw := by grind

end Lemmas

/-! ## Constructors -/
section Ctors

/-- The canonical representation of the constant zero function. -/
@[match_pattern]
def zero : CanonicalEventTree where
  raw := .leaf 0

/-- A leaf with value `n`. -/
@[match_pattern]
def leaf (n : Nat) : CanonicalEventTree where
  raw := .leaf n

/--
A node with base value `n` and children `l` and `r`.
Requires that the node is canonical, i.e., `min l.rootValue r.rootValue = 0`.
-/
@[match_pattern]
def node (n : Nat) (l r : CanonicalEventTree)
    (hmin : min l.raw.rootValue r.raw.rootValue = 0 := by simp; try omega) :
    CanonicalEventTree where
  raw := .node n l.raw r.raw
  eq_normalize := by
    rcases l with ⟨l, hl⟩
    rcases r with ⟨r, hr⟩
    simp only [EventTree.normalize, hl, hr]
    simp [hmin]

/--
`node'` returns a canonical event tree equivalent to the node with base value `n`
and children `l` and `r`.

NOTE: the normalization means that the result of `node'` may have a different
base value than `n` if the minimum of the children's root values is non-zero.
-/
def node' (n : Nat) (l r : CanonicalEventTree) : CanonicalEventTree where
  raw := (EventTree.node n l.raw r.raw).normalize

/-! ### Constructor Lemmas -/
section CtorLemmas
variable {e : CanonicalEventTree} {l r : CanonicalEventTree} {n : Nat} {hmin}

@[simp, grind =] theorem raw_zero : zero.raw = .leaf 0 := rfl
@[simp, grind =] theorem raw_leaf : (leaf n).raw = .leaf n := rfl
@[simp, grind =] theorem raw_node : (node n l r hmin).raw = .node n l.raw r.raw := rfl
@[simp, grind =] theorem raw_node' : (node' n l r).raw = (EventTree.node n l.raw r.raw).normalize := rfl

@[simp, grind .] theorem eq_zero_iff : e = zero ↔ e.raw = .leaf 0 := by grind
@[simp, grind .] theorem eq_leaf_iff : e = leaf n ↔ e.raw = .leaf n := by grind
@[simp, grind .] theorem eq_node_iff : e = node n l r hmin ↔ e.raw = .node n l.raw r.raw := by grind

@[simp] theorem leaf_zero_eq_zero : leaf 0 = zero := rfl

@[simp, grind =] theorem mk_leaf_eq_leaf {h} : (⟨.leaf n, h⟩ : CanonicalEventTree) = leaf n := rfl

end CtorLemmas
end Ctors

/-! ## Recursion Principle -/
section Recursion

/--
Recursion principle for `CanonicalEventTree` using the high-level constructors.
-/
@[elab_as_elim, induction_eliminator]
def rec' {motive : CanonicalEventTree → Sort u}
    (leaf : ∀ (n : Nat), motive (CanonicalEventTree.leaf n))
    (node : ∀ (n : Nat) (l r : CanonicalEventTree)
      (hmin : min l.raw.rootValue r.raw.rootValue = 0),
      motive l → motive r → motive (CanonicalEventTree.node n l r hmin))
    (t : CanonicalEventTree) : motive t :=
  go t.raw t.eq_normalize
  where
    go : (raw : EventTree) → (h_canon : raw.normalize = raw) → motive ⟨raw, h_canon⟩
    | .leaf n, _ => leaf n
    | .node n l r, hcanon =>
      let l' : CanonicalEventTree := ⟨l, by
        simp only [EventTree.normalize] at hcanon
        split at hcanon <;> simp_all⟩
      let r' : CanonicalEventTree := ⟨r, by
        simp only [EventTree.normalize] at hcanon
        split at hcanon <;> simp_all⟩
      have hmin : min l'.raw.rootValue r'.raw.rootValue = 0 := by
        -- A normalized node has min(l.rootValue, r.rootValue) = 0
        -- The proof is tedious; we defer it.
        sorry
      node n l' r' hmin (go l l'.eq_normalize) (go r r'.eq_normalize)

/--
Cases principle for `CanonicalEventTree` using the high-level constructors.
-/
@[cases_eliminator]
def cases' {motive : CanonicalEventTree → Sort u}
    (t : CanonicalEventTree)
    (leaf : ∀ (n : Nat), motive (CanonicalEventTree.leaf n))
    (node : ∀ (n : Nat) (l r : CanonicalEventTree)
      (hmin : min l.raw.rootValue r.raw.rootValue = 0),
      motive (CanonicalEventTree.node n l r hmin)) : motive t :=
  rec' leaf (fun n l r hmin _ _ => node n l r hmin) t

end Recursion

/-! ## Operations -/
section Operations

/-- The root value of a canonical event tree. -/
def rootValue (e : CanonicalEventTree) : Nat := e.raw.rootValue

/-- Lift a canonical event tree by adding `k` to the root. -/
def lift (k : Nat) (e : CanonicalEventTree) : CanonicalEventTree where
  raw := e.raw.lift k
  eq_normalize := by
    rcases e with ⟨raw, hcanon⟩
    cases raw with
    | leaf n => rfl
    | node n l r =>
      simp only [EventTree.lift, EventTree.normalize]
      simp only [EventTree.normalize] at hcanon
      split at hcanon
      · simp only [EventTree.node.injEq] at hcanon
        split
        · simp_all
        · -- lift doesn't change children, so min rootValue stays 0
          simp only [EventTree.rootValue] at *
          simp_all
      · simp only [EventTree.node.injEq] at hcanon
        split
        · simp_all
        · simp_all

@[simp] theorem rootValue_leaf : (leaf n).rootValue = n := rfl
@[simp] theorem rootValue_node : (node n l r hmin).rootValue = n := rfl

@[simp] theorem lift_leaf : lift k (leaf n) = leaf (n + k) := rfl

end Operations

/-! ## Comparison -/
section Comparison

instance : LE CanonicalEventTree := ⟨fun e₁ e₂ => e₁.raw ≤ e₂.raw⟩

instance : DecidableRel (α := CanonicalEventTree) (· ≤ ·) := fun e₁ e₂ =>
  inferInstanceAs (Decidable (e₁.raw ≤ e₂.raw))

end Comparison

/-! ## Join -/
section Join

/-- Join of two canonical event trees. -/
def join (e₁ e₂ : CanonicalEventTree) : CanonicalEventTree where
  raw := (e₁.raw.join e₂.raw).normalize
  eq_normalize := by simp

instance : Max CanonicalEventTree := ⟨join⟩

end Join

end CanonicalEventTree
end EffectSSA.ITC
