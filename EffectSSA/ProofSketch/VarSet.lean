module

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice

/-!
# VarSet
-/
namespace EffectSSA.ProofSketch

/-- `VarId` is the type of variables. -/
public structure VarId where
  raw : String
  deriving DecidableEq, Hashable
public instance : ToString VarId where toString := VarId.raw

/-- `VarSet` is a set of variables. -/
public def VarSet := Set VarId

/-!
For some reason, having the following definitions be computable requires the relevant definitions to
be exposed, which would require publicly importing Finset from Mathlib.
We don't want this, and don't actually need to compute with VarSet anyway,
so we conceed and make everything noncomputable.

The one use-case for which computability would've been nice, is to show decidability of, e.g,
the membership relation. This is not strictly needed, though.

The error raised when things are computable mentions that it is a compiler limitation that may be
addressed in the future, rather than a fundamental requirement, at which time we could have
this be computable.
-/
noncomputable section

namespace VarSet

/-! ### Internal API-/

def toSet : VarSet → Set VarId := id
def ofSet : Set VarId → VarSet := id

section Lemmas

theorem ofSet_toSet (A : VarSet) : ofSet (toSet A) = A := by rfl

end Lemmas

public section

/-! ### Standard Set Operations -/

def Subset (A B : VarSet) := A.toSet ⊆ B.toSet
instance : HasSubset VarSet where Subset := Subset

def union (A B : VarSet) : VarSet := ofSet <| A.toSet ∪ B.toSet
instance : Union VarSet where union := union

def inter (A B : VarSet) : VarSet := ofSet <| A.toSet ∩ B.toSet
instance : Inter VarSet where inter := inter

def empty : VarSet := ofSet ∅
instance : EmptyCollection VarSet where emptyCollection := empty

def singleton (v : VarId) : VarSet := ofSet { v }
instance : Singleton VarId VarSet where singleton := singleton

def insert (v : VarId) (V : VarSet) : VarSet := ofSet (Set.insert v V.toSet)
instance : Insert VarId VarSet where insert := insert

def Mem (A : VarSet) (v : VarId) := v ∈ A.toSet
instance : Membership VarId VarSet where mem := Mem

def sdiff (A B : VarSet) := ofSet <| A.toSet \ B.toSet
instance : Sub VarSet where sub := sdiff
-- ^ N.B: we use `-` notation over `\` set difference since the latter is
--        is defined in Mathlib

section Lemmas
variable {A B C : VarSet}

/-! ### ext -/

@[simp, grind =] private theorem mem_toSet (x : VarId) (A : VarSet) :
    x ∈ A.toSet ↔ x ∈ A := by rfl
@[simp, grind =] private theorem mem_ofSet (x : VarId) (A : Set VarId) :
    x ∈ (ofSet A) ↔ x ∈ A := by rfl

@[ext, grind ext]
theorem ext (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := by
  show A.toSet = B.toSet
  ext x
  simpa using h x

/-! ### mem -/

@[simp, grind =] theorem mem_singleton : x ∈ ({ y } : VarSet) ↔ x = y := by rfl
@[simp, grind =] theorem mem_insert : x ∈ (Insert.insert y A) ↔ x = y ∨ x ∈ A := by rfl

/-! ### empty -/
section Empty

@[local grind =] private theorem empty_def : (∅ : VarSet) = ofSet ∅ := by rfl

@[simp, grind .] theorem not_mem_empty : v ∉ (∅ : VarSet) := by grind

theorem eq_empty_iff : A = ∅ ↔ (∀ v, v ∉ A) := by
  constructor
  · rintro rfl; grind
  · intro h; ext; grind

end Empty

/-! ### union -/
section Union

@[local grind =] private theorem union_def : A ∪ B = ofSet (A.toSet ∪ B.toSet) := by rfl

@[simp, grind =] theorem mem_union : v ∈ A ∪ B ↔ v ∈ A ∨ v ∈ B := by grind

@[simp, grind =] theorem empty_union : ∅ ∪ A = A := by ext; grind
@[simp, grind =] theorem union_empty : A ∪ ∅ = A := by ext; grind
@[simp, grind =] theorem union_self  : A ∪ A = A := by ext; grind

@[grind =] theorem union_assoc : A ∪ B ∪ C = A ∪ (B ∪ C) := by ext; grind
@[grind =] theorem union_comm : A ∪ B = B ∪ A := by ext; grind

@[simp] theorem union_eq_empty_iff : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := by
  simp [eq_empty_iff]; grind

end Union

/-! ### inter -/
section Inter

@[local grind =] private theorem inter_def : A ∩ B = ofSet (A.toSet ∩ B.toSet) := by rfl

@[simp, grind =] theorem mem_inter : v ∈ A ∩ B ↔ v ∈ A ∧ v ∈ B := by grind

@[simp, grind =] theorem empty_inter : ∅ ∩ A = ∅ := by ext; grind
@[simp, grind =] theorem inter_empty : A ∩ ∅ = ∅ := by ext; grind
@[simp, grind =] theorem inter_self  : A ∩ A = A := by ext; grind

@[grind =] theorem inter_assoc : A ∩ B ∩ C = A ∩ (B ∩ C) := by ext; grind
@[grind =] theorem inter_comm : A ∩ B = B ∩ A := by ext; grind

@[grind =] theorem union_inter : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by ext; grind
@[grind =] theorem inter_union : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by ext; grind

end Inter

/-! ### subset -/

@[grind →] theorem mem_of_subset_of_mem : A ⊆ B → a ∈ A → a ∈ B :=
  Set.mem_of_subset_of_mem

@[grind =] theorem subset_iff : A ⊆ B ↔ (∀ x, x ∈ A → x ∈ B) := by
  show A.toSet ⊆ B.toSet ↔ ∀ x, x ∈ A.toSet → x ∈ B.toSet
  grind
theorem subset_intro : (∀ x, x ∈ A → x ∈ B) → A ⊆ B := by grind

@[simp, grind .] theorem empty_subset : (∅ : VarSet) ⊆ A := by grind

/-! ### sdiff -/

@[simp, grind =] theorem mem_sdiff : v ∈ A - B ↔ v ∈ A ∧ v ∉ B := Set.mem_sdiff v

@[simp, grind =] theorem empty_sdiff : (∅ : VarSet) - A = ∅ := by ext; simp
@[simp, grind =] theorem sdiff_empty : A - (∅ : VarSet) = A := by ext; simp

end Lemmas

/-! ### Disjoint -/

@[expose] def Disjoint (A B : VarSet) : Prop :=
  A ∩ B = ∅

section Lemmas
variable {A B : VarSet}
attribute [local grind] Disjoint

@[simp, grind .] theorem empty_disjoint : Disjoint ∅ A := by grind
@[simp, grind .] theorem disjoint_empty : Disjoint A ∅ := by grind
@[simp, grind =] theorem disjoint_self : A.Disjoint A ↔ A = ∅ := by grind

@[simp, grind =] theorem singleton_disjoint_iff : ({ x } : VarSet).Disjoint A ↔ x ∉ A := by
  simp [Disjoint, eq_empty_iff]

@[simp, grind =] theorem union_disjoint :
    Disjoint (A ∪ B) C ↔ Disjoint A C ∧ Disjoint B C := by
  grind

@[simp, grind =] theorem disjoint_union :
    Disjoint A (B ∪ C) ↔ Disjoint A B ∧ Disjoint A C := by
  grind

@[grind =] theorem disjoint_symm : A.Disjoint B ↔ B.Disjoint A := by grind

theorem inter_eq_of_disjoint (h : A.Disjoint B) : A ∩ B = ∅ := by grind
grind_pattern inter_eq_of_disjoint => A.Disjoint B, A ∩ B

theorem disjoint_iff_mem : A.Disjoint B ↔ (∀ x, ¬(x ∈ A ∧ x ∈ B)) := by
  simp [Disjoint, eq_empty_iff]

@[grind .] theorem disjoint_intro : (∀ x, ¬(x ∈ A ∧ x ∈ B)) → A.Disjoint B := by grind

@[grind →] theorem not_mem_of_disjoint (h : A.Disjoint B) {x} :
    x ∈ A → x ∉ B := by
  grind [disjoint_iff_mem]

@[grind →, grind <=]
theorem disjoint_of_supset_disjoint : A ⊆ B → B.Disjoint C → A.Disjoint C := by
  grind [disjoint_iff_mem]


end Lemmas

/-! ### setOf -/

def setOf (P : VarId →Prop) : VarSet :=
  ofSet <| _root_.setOf P

/-- Adapted from Mathlib Set notation -/
scoped syntax (name := varSetBuilder) (priority := high) "{" term " | " term "}" : term
scoped macro_rules (kind := varSetBuilder)
  | `( { $x:ident | $p } ) => `(setOf fun $x => $p)

section Lemmas

@[simp, grind =] theorem mem_setOf : x ∈ setOf P ↔ P x := by simp [setOf]

end Lemmas

/-! ### Map -/

/--
Given a function `f : VarId →VarSet` and a set `A : VarSet`, return the set
  `{ f a | a ∈ A }`
-/
@[expose, grind] def flatMap (f : VarId →VarSet) (A : VarSet) : VarSet :=
  { x | ∃ y ∈ A, x ∈ f y }

/--
Given a function `f : α → VarSet` and a list `as : List α`, return the set
  `{ f a | a ∈ A }`
-/
@[expose, grind] def ofListMap [DecidableEq α] (f : α → VarSet) (as : List α) : VarSet :=
  { x | ∃ y ∈ as, x ∈ f y }

section Lemmas
variable {A : VarSet}

@[simp, grind =] theorem mem_flatMap : x ∈ A.flatMap f ↔ ∃ y ∈ A, x ∈ f y := by
  simp [flatMap]

@[simp, grind =] theorem mem_ofListMap {as : List α} [DecidableEq α] :
    x ∈ ofListMap f as ↔ ∃ y ∈ as, x ∈ f y := by
  simp [ofListMap]

end Lemmas

end
end VarSet
