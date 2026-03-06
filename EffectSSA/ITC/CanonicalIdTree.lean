import EffectSSA.ITC.IdTree

/-!
# Canonical Id Trees

-/
namespace EffectSSA.ITC

/--
A `CanonicalIdTree` is an `IdTree` which is guaranteed to be in normal form.
-/
structure CanonicalIdTree where
  raw : IdTree
  eq_normalize : raw.normalize = raw := by solve | rfl | simp; try grind
  deriving DecidableEq

namespace CanonicalIdTree

/-! ## Basic Lemmas -/
section Lemmas
variable {i j : CanonicalIdTree}

attribute [grind =] CanonicalIdTree.eq_normalize

@[ext, grind ext]
theorem ext : i.raw = j.raw → i = j := by
  grind [cases CanonicalIdTree]

@[simp] theorem eq_iff_raw_eq : i = j ↔ i.raw = j.raw := by grind

@[simp, grind .] theorem mk_eq_iff {raw : IdTree} {h : raw.normalize = raw} {j : CanonicalIdTree} :
    ⟨raw, h⟩ = j ↔ raw = j.raw := by grind

@[simp, grind .] theorem eq_mk_iff {i : CanonicalIdTree} {raw : IdTree} {h : raw.normalize = raw} :
    i = ⟨raw, h⟩ ↔ i.raw = raw := by grind

end Lemmas

/-! ## Constructors -/
section Ctors

/-- The canonical representation of the empty set (i.e., `zero`). -/
@[match_pattern]
def zero : CanonicalIdTree where
  raw := .zero

/-- The canonical representation of the full interval (i.e., `one`). -/
@[match_pattern]
def one : CanonicalIdTree where
  raw := .one

/--
A node with left child `l` and right child `r`.
Requires that the node is canonical, i.e., it's not allowed for both children to
be `zero` or both to be `one`.
-/
@[match_pattern]
def node (l r : CanonicalIdTree)
    (hz : ¬(l = zero ∧ r = zero) := by simp; try grind)
    (ho : l ≠ one ∨ r ≠ one := by simp; try grind) :
    CanonicalIdTree where
  raw := .node l.raw r.raw
  eq_normalize := by
    rcases l with ⟨l, hl⟩
    rcases r with ⟨r, hr⟩
    replace hz : ¬(l = .zero ∧ r = .zero) := by simpa using hz
    replace ho : l ≠ .one ∨ r ≠ .one := by simpa using ho
    grind [IdTree.normalize]

/--
`node'` returns an id tree equivalent to the node with children `l` and `r`.

NOTE: the normalization means that the result of `node'` is not necessarily an
actual node in the tree! E.g., if `l = r = zero`, then the result is just a
single `zero` leaf.
-/
def node' (l r : CanonicalIdTree) : CanonicalIdTree where
  raw := (IdTree.node l.raw r.raw).normalize

/-! ### Constructor Lemmas -/
section CtorLemmas
variable {i l r : CanonicalIdTree} {hz ho}

@[simp, grind =] theorem raw_zero : zero.raw = .zero := rfl
@[simp, grind =] theorem raw_one  : one.raw = .one := rfl
@[simp, grind =] theorem raw_node : (node l r hz ho).raw = .node l.raw r.raw := rfl
@[simp, grind =] theorem raw_node' : (node' l r).raw = .normalize (.node l.raw r.raw) := rfl

@[simp, grind .] theorem eq_zero_iff :           i = zero ↔ i.raw = .zero             := by grind
@[simp, grind .] theorem eq_one_iff  :            i = one ↔ i.raw = .one              := by grind
@[simp, grind .] theorem eq_node_iff : i = node l r hz ho ↔ i.raw = .node l.raw r.raw := by grind

@[simp] theorem zero_ne_one : (zero : CanonicalIdTree) ≠ one := by simp
@[simp] theorem one_ne_zero : (one : CanonicalIdTree) ≠ zero := by simp
@[simp] theorem node_ne_zero : node l r hz ho ≠ zero := by simp
@[simp] theorem node_ne_one : node l r hz ho ≠ one := by simp
@[simp] theorem zero_ne_node : zero ≠ node l r hz ho := by simp

@[simp] theorem one_ne_node : one ≠ node l r hz ho := by
  intro heq; cases heq

theorem node_injective :
    node l₁ r₁ hz₁ ho₁ = node l₂ r₂ hz₂ ho₂ → l₁ = l₂ ∧ r₁ = r₂ := by
  grind

@[simp, grind =] theorem mk_zero_eq_zero {h} : (⟨.zero, h⟩ : CanonicalIdTree) = zero := by rfl
@[simp, grind =] theorem mk_one_eq_one {h} : (⟨.one, h⟩ : CanonicalIdTree) = one := by rfl

@[simp, grind =] theorem mk_node_eq_node {l r : IdTree} (h : (IdTree.node l r).normalize = .node l r) :
    (⟨.node l r, h⟩ : CanonicalIdTree) = node ⟨l, by grind⟩ ⟨r, by grind⟩ := by rfl

@[simp, grind =] theorem mk_normalize_node {l r : IdTree} :
    ⟨(IdTree.node l r).normalize, by grind⟩ = node' ⟨l.normalize, by grind⟩ ⟨r.normalize, by grind⟩ := by
  simp [node', IdTree.normalize]

/-! #### node' -/

@[simp, grind =] theorem one_node'_one : node' one one = one := by grind [node', IdTree.normalize]
@[simp, grind =] theorem zero_node'_zero : node' zero zero = zero := by grind [node', IdTree.normalize]

@[simp, grind =] theorem node'_eq_node_of (hz : ¬(l = zero ∧ r = zero)) (ho : l ≠ one ∨ r ≠ one) :
    node' l r = node l r hz ho := by grind [node']

end CtorLemmas
end Ctors

/-! ## Recursion Principle -/
section Recursion

/--
Recursion principle for `CanonicalIdTree` using the high-level constructors.
-/
@[elab_as_elim, induction_eliminator]
def rec' {motive : CanonicalIdTree → Sort u}
    (zero : motive CanonicalIdTree.zero)
    (one : motive CanonicalIdTree.one)
    (node : ∀ (l r : CanonicalIdTree) (hz : ¬(l = .zero ∧ r = .zero)) (ho : l ≠ .one ∨ r ≠ .one),
      motive l → motive r → motive (CanonicalIdTree.node l r hz ho))
    (t : CanonicalIdTree) : motive t :=
  go t.raw t.eq_normalize
  where
    go : (raw : IdTree) → (h_canon : raw.normalize = raw) → motive ⟨raw, h_canon⟩
    | .zero, _ => zero
    | .one, _ => one
    | .node l r, hcanon =>
      let l : CanonicalIdTree := ⟨l, by grind⟩
      let r : CanonicalIdTree := ⟨r, by grind⟩
      have ho := by simp; grind
      have hz := by simp; grind
      node l r ho hz (go l.1 l.2) (go r.1 r.2)

/--
Cases principle for `CanonicalIdTree` using the high-level constructors.
-/
@[cases_eliminator]
def cases' {motive : CanonicalIdTree → Sort u}
    (t : CanonicalIdTree)
    (zero : motive CanonicalIdTree.zero)
    (one : motive CanonicalIdTree.one)
    (node : ∀ (l r : CanonicalIdTree) (hz : ¬(l = .zero ∧ r = .zero)) (ho : l ≠ .one ∨ r ≠ .one),
      motive (CanonicalIdTree.node l r hz ho)) : motive t :=
  rec' zero one (fun l r hz ho _ _ => node l r hz ho) t

end Recursion

end CanonicalIdTree
end EffectSSA.ITC
