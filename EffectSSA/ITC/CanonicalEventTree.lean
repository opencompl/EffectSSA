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

/-! ## Basic Structural Lemmas -/
section Lemmas
variable {e f : CanonicalEventTree}

attribute [simp, grind =_] CanonicalEventTree.eq_normalize

@[ext, grind ext]
theorem ext : e.raw = f.raw → e = f := by
  grind [cases CanonicalEventTree]

@[simp] theorem eq_iff_raw_eq : e = f ↔ e.raw = f.raw := by grind

@[simp, grind .] theorem mk_eq_iff {raw : EventTree} {h : raw.normalize = raw} {f : CanonicalEventTree} :
    ⟨raw, h⟩ = f ↔ raw = f.raw := by grind

@[simp, grind .] theorem eq_mk_iff {e : CanonicalEventTree} {raw : EventTree} {h : raw.normalize = raw} :
    e = ⟨raw, h⟩ ↔ e.raw = raw := by grind

end Lemmas

/-! ## Basic Definitions -/
section Defs

@[grind] def rootValue (e : CanonicalEventTree) : Nat := e.raw.rootValue
@[grind] def maxValue (e : CanonicalEventTree) : Nat := e.raw.maxValue

def lift (k : Nat) (e : CanonicalEventTree) : CanonicalEventTree where
  raw := e.raw.lift k
  eq_normalize := by
    rcases e with ⟨_|_, _⟩ <;> grind

def sink (e : CanonicalEventTree) (k : Nat) (hk : k ≤ e.rootValue) : CanonicalEventTree where
  raw := e.raw.sink k hk

section Lemmas
variable {e : CanonicalEventTree} {n m k : Nat}

attribute [local grind] sink rootValue maxValue

/-! ### Raw projection lemmas -/

@[simp, grind =] theorem raw_sink : (e.sink k hk).raw = e.raw.sink k hk := rfl
@[simp, grind =] theorem raw_lift : (e.lift k).raw = e.raw.lift k := rfl

@[simp, grind =] theorem sink_zero : e.sink 0 hk = e := by grind
@[simp, grind =] theorem lift_zero : e.lift 0 = e := by grind

@[simp, grind =] theorem rootValue_sink : (e.sink k hk).rootValue = e.rootValue - k := by grind
@[simp, grind =] theorem maxValue_sink : (e.sink k hk).maxValue = e.maxValue - k := by grind

@[simp] theorem rootValue_le_maxValue : e.rootValue ≤ e.maxValue := by grind
grind_pattern rootValue_le_maxValue => e.rootValue, e.maxValue

end Lemmas
end Defs

/-! ## Constructors -/
section Ctors

/-- A leaf with value `n`. -/
@[match_pattern]
def leaf (n : Nat) : CanonicalEventTree where
  raw := .leaf n

/-- The canonical representation of the constant zero function. -/
@[match_pattern]
abbrev zero : CanonicalEventTree := leaf 0

/--
A node with base value `n` and children `l` and `r`.
Requires that the node is canonical, i.e., `min l.rootValue r.rootValue = 0`.
-/
@[match_pattern]
def node (n : Nat) (l r : CanonicalEventTree)
    (hmin : min l.raw.rootValue r.raw.rootValue = 0 := by simp; try grind) :
    CanonicalEventTree where
  raw := .node n l.raw r.raw
  eq_normalize := by simp [EventTree.normalize_node]; grind

/--
`node'` returns a canonical event tree equivalent to the node with base value `n`
and children `l` and `r`.

NOTE: the normalization means that the result of `node'` may have a different
base value than `n` if the minimum of the children's root values is non-zero.
-/
def node' (n : Nat) (l r : CanonicalEventTree) : CanonicalEventTree :=
  let m := min l.rootValue r.rootValue
  let l' := l.sink m (by grind)
  let r' := r.sink m (by grind)
  node (n + m) l' r'

/-! ### Constructor Lemmas -/
section CtorLemmas
variable {e : CanonicalEventTree} {l r : CanonicalEventTree} {n : Nat} {hmin}

@[simp, grind =] theorem raw_zero : zero.raw = .leaf 0 := rfl
@[simp, grind =] theorem raw_leaf : (leaf n).raw = .leaf n := rfl
@[simp, grind =] theorem raw_node : (node n l r hmin).raw = .node n l.raw r.raw := rfl
@[simp, grind =] theorem raw_node' : (node' n l r).raw = (EventTree.node n l.raw r.raw).normalize := by
  grind [node']

@[simp] theorem eq_zero_iff : e = zero ↔ e.raw = .leaf 0 := by grind
@[simp] theorem eq_leaf_iff : e = leaf n ↔ e.raw = .leaf n := by grind
@[simp] theorem eq_node_iff : e = node n l r hmin ↔ e.raw = .node n l.raw r.raw := by grind

@[simp] theorem leaf_zero_eq_zero : leaf 0 = zero := rfl

@[simp, grind =] theorem mk_leaf_eq_leaf {h} : (⟨.leaf n, h⟩ : CanonicalEventTree) = leaf n := rfl

/-! #### Basic Definitions -/

@[simp, grind =] theorem rootValue_leaf : (leaf n).rootValue = n := rfl
@[simp, grind =] theorem rootValue_node : (node n l r hmin).rootValue = n := rfl

@[simp, grind =] theorem maxValue_leaf : (leaf n).maxValue = n := rfl
@[simp, grind =] theorem maxValue_node : (node n l r hmin).maxValue = n + max l.maxValue r.maxValue := rfl

@[simp, grind =] theorem lift_leaf : lift k (leaf n) = leaf (n + k) := rfl
@[simp, grind =] theorem lift_node : lift k (node n l r hmin) = node (n + k) l r hmin := rfl

@[simp, grind =] theorem sink_leaf : (leaf n).sink k hk = leaf (n - k) := rfl
@[simp, grind =] theorem sink_node : (node n l r hmin).sink k hk = node (n - k) l r hmin := rfl

end CtorLemmas
end Ctors

/-! ## Recursion Principle -/
section Recursion

/--
Recursion principle for `CanonicalEventTree` using the high-level constructors.
-/
@[elab_as_elim, induction_eliminator]
def rec' {motive : CanonicalEventTree → Sort u}
    (leaf : ∀ (n : Nat), motive (leaf n))
    (node : ∀ (n : Nat) (l r : CanonicalEventTree)
      (hmin : min l.raw.rootValue r.raw.rootValue = 0),
      motive l → motive r → motive (node n l r hmin))
    (t : CanonicalEventTree) : motive t :=
  go t.raw t.eq_normalize
  where
    go : (raw : EventTree) → (h_canon : raw.normalize = raw) → motive ⟨raw, h_canon⟩
    | .leaf n, _ => leaf n
    | .node n l r, hcanon =>
      let l' : CanonicalEventTree := ⟨l, by grind⟩
      let r' : CanonicalEventTree := ⟨r, by grind⟩
      have hmin : min l'.raw.rootValue r'.raw.rootValue = 0 := by grind
      node n l' r' hmin (go l'.1 l'.2) (go r'.1 r'.2)

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

/-! ## Denotation -/

/-!
## Denotation
-/
section Denote

def denote (e : CanonicalEventTree) : Rat → Nat := e.raw.denote

section DenoteLemmas
variable {e l r: CanonicalEventTree} {n : Nat} {x : Rat}

attribute [local grind] denote


@[grind =] theorem denote_leaf : (leaf n).denote x = if 0 ≤ x ∧ x < 1 then n else 0 := by rfl
@[grind =] theorem denote_node :
    (node n l r hmin).denote x
    = if 0 ≤ x ∧ x < 0.5 then
        n + l.denote (2 * x)
      else if 0.5 ≤ x ∧ x < 1 then
        n + r.denote (2 * x - 1)
      else
        0 := by rfl

@[simp, grind =]
theorem denote_sink : (e.sink k hk).denote x = e.denote x - k :=
  EventTree.denote_sink

@[simp, grind =] theorem denote_eq_zero_of (hx : x < 0 ∨ 1 ≤ x) : e.denote x = 0 := by
  cases e <;> grind

@[simp, grind =] theorem denote_leaf_of (hx : 0 ≤ x ∧ x < 1) : (leaf n).denote x = n := by grind
@[simp, grind =] theorem denote_node_of_left (hx : 0 ≤ x ∧ x < 0.5) :
    (node n l r hmin).denote x = n + l.denote (2 * x) := by grind
@[simp, grind =] theorem denote_node_of_right (hx : 0.5 ≤ x ∧ x < 1) :
    (node n l r hmin).denote x = n + r.denote (2 * x - 1) := by grind

@[simp, grind! .] theorem rootValue_le_denote (hx : 0 ≤ x ∧ x < 1) : e.rootValue ≤ e.denote x :=
  EventTree.rootValue_le_denote hx

@[simp, grind =] theorem denote_node'_of (hx : 0 ≤ x ∧ x < 1) :
    (node' n l r).denote x = n + l.denote (2 * x) + r.denote (2 * x - 1) := by
  by_cases hx' : x < 0.5
  · have : 0 ≤ x ∧ x < 0.5 := by grind
    have : 2 * x - 1 < 0 := by grind
    grind [node']
  · have : 0.5 ≤ x ∧ x < 1 := by grind
    have : 2 * x ≥ 1 := by grind
    grind [node']

end DenoteLemmas
end Denote
end CanonicalEventTree
end EffectSSA.ITC
