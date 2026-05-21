module

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Lattice

/-!
# VarSet
-/
namespace EffectSSA.ProofSketch

/-- `VarSet` is a set of variables. -/
public def VarSet ν := Set ν

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

def toSet : VarSet ν → Set ν := id
def ofSet : Set ν → VarSet ν := id

section Lemmas

theorem ofSet_toSet (A : VarSet ν) : ofSet (toSet A) = A := by rfl

end Lemmas

public section

/-! ### Standard Set Operations -/

def Subset (A B : VarSet ν) := A.toSet ⊆ B.toSet
instance : HasSubset (VarSet ν) where Subset := Subset

def union (A B : VarSet ν) : VarSet ν := ofSet <| A.toSet ∪ B.toSet
instance : Union (VarSet ν) where union := union

def inter (A B : VarSet ν) : VarSet ν := ofSet <| A.toSet ∩ B.toSet
instance : Inter (VarSet ν) where inter := inter

def empty : VarSet ν := ofSet ∅
instance : EmptyCollection (VarSet ν) where emptyCollection := empty

def singleton (v : ν) : VarSet ν := ofSet { v }
instance : Singleton ν (VarSet ν) where singleton := singleton

def Mem (A : VarSet ν) (v : ν) := v ∈ A.toSet
instance : Membership ν (VarSet ν) where mem := Mem

def sdiff (A B : VarSet ν) := ofSet <| A.toSet \ B.toSet
instance : Sub (VarSet ν) where sub := sdiff
-- ^ N.B: we use `-` notation over `\` set difference since the latter is
--        is defined in Mathlib
-- TODO: actually it seems SDiff just exists in core, I should switch over

section Lemmas
variable {A B C : VarSet ν}

/-! ### ext -/

@[simp, grind =] private theorem mem_toSet (x : ν) (A : VarSet ν) :
    x ∈ A.toSet ↔ x ∈ A := by rfl
@[simp, grind =] private theorem mem_ofSet (x : ν) (A : Set ν) :
    x ∈ (ofSet A) ↔ x ∈ A := by rfl

@[ext, grind ext]
theorem ext (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := by
  show A.toSet = B.toSet
  ext x
  simpa using h x

/-! ### empty -/

@[simp, grind .] theorem not_mem_empty : v ∉ (∅ : VarSet ν) := by grind

theorem eq_empty_iff : A = ∅ ↔ (∀ v, v ∉ A) := by
  constructor
  · rintro rfl; grind
  · intro h; ext; grind

/-! ### union -/

@[simp, grind =] theorem mem_union : v ∈ A ∪ B ↔ v ∈ A ∨ v ∈ B := by grind

@[simp, grind =] theorem empty_union : ∅ ∪ A = A := by ext; grind
@[simp, grind =] theorem union_empty : A ∪ ∅ = A := by ext; grind
@[simp, grind =] theorem union_self  : A ∪ A = A := by ext; grind

@[grind =] theorem union_assoc : A ∪ B ∪ C = A ∪ (B ∪ C) := by ext; grind
@[grind =] theorem union_comm : A ∪ B = B ∪ A := by ext; grind

@[simp] theorem union_eq_empty_iff : A ∪ B = ∅ ↔ A = ∅ ∧ B = ∅ := by
  simp [eq_empty_iff]; grind

/-! ### inter -/

@[simp, grind =] theorem mem_inter : v ∈ A ∩ B ↔ v ∈ A ∧ v ∈ B := by grind

@[simp, grind =] theorem empty_inter : ∅ ∩ A = ∅ := by ext; grind
@[simp, grind =] theorem inter_empty : A ∩ ∅ = ∅ := by ext; grind
@[simp, grind =] theorem inter_self  : A ∩ A = A := by ext; grind

@[grind =] theorem inter_assoc : A ∩ B ∩ C = A ∩ (B ∩ C) := by ext; grind
@[grind =] theorem inter_comm : A ∩ B = B ∩ A := by ext; grind

@[grind =] theorem union_inter : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by ext; grind
@[grind =] theorem inter_union : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by ext; grind

/-! ### subset -/

@[grind →] theorem mem_of_subset_of_mem : A ⊆ B → a ∈ A → a ∈ B :=
  Set.mem_of_subset_of_mem

@[grind =] theorem subset_iff : A ⊆ B ↔ (∀ x, x ∈ A → x ∈ B) := by
  show A.toSet ⊆ B.toSet ↔ ∀ x, x ∈ A.toSet → x ∈ B.toSet
  grind
theorem subset_intro : (∀ x, x ∈ A → x ∈ B) → A ⊆ B := by grind

@[simp, grind .] theorem empty_subset : (∅ : VarSet ν) ⊆ A := by grind

/-! ### sdiff -/

@[simp, grind =] theorem mem_sdiff : v ∈ A - B ↔ v ∈ A ∧ v ∉ B := Set.mem_diff v

@[simp, grind =] theorem empty_sdiff : (∅ : VarSet ν) - A = ∅ := by ext; simp
@[simp, grind =] theorem sdiff_empty : A - (∅ : VarSet ν) = A := by ext; simp

end Lemmas

/-! ### Disjoint -/

@[expose] def Disjoint (A B : VarSet ν) : Prop :=
  A ∩ B = ∅

section Lemmas
variable {A B : VarSet ν}
attribute [local grind] Disjoint

@[simp, grind .] theorem empty_disjoint : Disjoint ∅ A := by grind
@[simp, grind .] theorem disjoint_empty : Disjoint A ∅ := by grind
@[simp, grind =] theorem disjoint_self : A.Disjoint A ↔ A = ∅ := by grind

@[simp, grind =] theorem union_disjoint :
    Disjoint (A ∪ B) C ↔ Disjoint A C ∧ Disjoint B C := by
  simp [Disjoint, union_inter]

@[simp, grind =] theorem disjoint_union :
    Disjoint A (B ∪ C) ↔ Disjoint A B ∧ Disjoint A C := by
  simp [Disjoint, inter_union]

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

def setOf (P : ν → Prop) : VarSet ν :=
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
Given a function `f : Var → VarSet ν` and a set `A : VarSet ν`, return the set
  `{ f a | a ∈ A }`
-/
@[expose, grind] def flatMap (f : ν → VarSet ν) (A : VarSet ν) : VarSet ν :=
  { x | ∃ y ∈ A, x ∈ f y }

/--
Given a function `f : α → VarSet ν` and a list `as : List α`, return the set
  `{ f a | a ∈ A }`
-/
@[expose, grind] def ofListMap [DecidableEq α] (f : α → VarSet ν) (as : List α) : VarSet ν :=
  { x | ∃ y ∈ as, x ∈ f y }

section Lemmas
variable {A : VarSet ν}

@[simp, grind =] theorem mem_flatMap : x ∈ A.flatMap f ↔ ∃ y ∈ A, x ∈ f y := by
  simp [flatMap]

@[simp, grind =] theorem mem_ofListMap {as : List α} [DecidableEq α] :
    x ∈ ofListMap f as ↔ ∃ y ∈ as, x ∈ f y := by
  simp [ofListMap]

end Lemmas

end
end VarSet
