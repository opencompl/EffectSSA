module

public import EffectSSA.ProofSketch.InstSeq
public import EffectSSA.ProofSketch.ProofSketch

namespace EffectSSA.ProofSketch
@[expose] public section
variable [SSA ι σ ν]

/-!
## Array Types
-/

structure InstArr (ι) [SSA ι σ ν] where
  toArray : Array (Inst ι)

structure InstSubarray (ι) [SSA ι σ ν] where
  start : Nat
  originalArray : Array (Inst ι)

/-!
## Subarray API
-/
namespace InstSubarray

def toSeq (is : InstSubarray ι) : InstSeq ι :=
  (is.originalArray.drop is.start).toList

/-- Return the number of instructions in the subarray. -/
@[grind]
def size (is : InstSubarray ι) : Nat :=
  is.originalArray.size - is.start

/--
Extracts an element from the subarray.

The index is relative to the start of the subarray, rather than the underlying array.
-/
instance : GetElem (InstSubarray ι) Nat (Inst ι) fun xs i => i < xs.size where
  getElem xs i h := xs.originalArray[i + xs.start]'(by grind)

@[grind =] theorem getElem_eq {is : InstSubarray ι} {k : Nat} {hk : k < is.size} :
    is[k] = is.originalArray[k + is.start]'(by grind) := by rfl

/--
Shrink the subarray by incrementing its starting index.
-/
def popFront (is : InstSubarray ι) : InstSubarray ι :=
  { is with start := is.start + 1 }

section Lemmas
variable {is : InstSubarray ι}

@[simp, grind =] theorem start_popFront : is.popFront.start = is.start + 1 := by rfl
@[simp, grind =] theorem originalArray_popFront :
    is.popFront.originalArray = is.originalArray := by rfl
@[simp, grind =] theorem size_popFront : is.popFront.size = is.size - 1 := by
  grind [popFront]


@[grind →] theorem toSeq_eq_nil_of_size : is.size = 0 → is.toSeq = [] := by
  simp [toSeq]; grind

@[grind →] theorem toSeq_eq_cons_size : (h : is.size ≠ 0) → is.toSeq = is[0] :: is.popFront.toSeq := by
  intro h
  have hlt : is.start < is.originalArray.size := by grind [size]
  have hdrop : ∀ (i : Nat),
      (is.originalArray.drop i).toList = is.originalArray.toList.drop i := by
    intro i
    show (is.originalArray.extract i is.originalArray.size).toList = _
    simp [Array.toList_extract, List.take_of_length_le]
  simp only [toSeq, popFront, getElem_eq, Nat.zero_add]
  rw [hdrop, hdrop, ← Array.getElem_toList]
  exact List.drop_eq_getElem_cons (by simpa using hlt)

end Lemmas

section Denote

instance : Denote (InstSubarray ι) (SEnv ι → SEnv ι) where
  denote is := ⟦is.toSeq⟧

@[grind =] theorem denote_eq {is : InstSubarray ι} : ⟦is⟧ = ⟦is.toSeq⟧ := by rfl

end Denote
end InstSubarray

/-!
## Array API
-/
namespace InstArr

@[inherit_doc Array.emptyWithCapacity]
def emptyWithCapacity (n : Nat) : InstArr ι :=
  ⟨.emptyWithCapacity n⟩

@[inherit_doc Array.empty]
def empty : InstArr ι := emptyWithCapacity 0

/-- Add a new instruction to the *bottom* of an instruction array. -/
def push (is : InstArr ι) (i : Inst ι) : InstArr ι :=
  ⟨is.toArray.push i⟩

abbrev size (is : InstArr ι) : Nat := is.toArray.size

abbrev toSubarray (is : InstArr ι) : InstSubarray ι where
  originalArray := is.toArray
  start := 0

/--
Convert an array of instruction into an `InstSeq`,
containing the same instructions in the same order.
-/
def toSeq (is : InstArr ι) : InstSeq ι :=
  is.toArray.toList

section Lemmas
variable {is : InstArr ι} {i : Inst ι}

@[simp, grind =]
theorem toSeq_push : (is.push i).toSeq = is.toSeq ++ [i] := by
  simp [toSeq, push]

@[simp, grind =] theorem toSeq_empty : (@empty ι).toSeq = [] := by rfl
@[simp, grind =] theorem toSeq_emptyWithCapacity : (emptyWithCapacity (ι:=ι) n).toSeq = [] := by rfl

@[simp, grind =] theorem toSeq_toSubarray : is.toSubarray.toSeq = is.toSeq := by
  simp [InstSubarray.toSeq, toSeq]

end Lemmas

section Denote

instance : Denote (InstArr ι) (SEnv ι → SEnv ι) where
  denote is := ⟦is.toSeq⟧

@[grind =] theorem denote_eq {is : InstArr ι} : ⟦is⟧ = ⟦is.toSeq⟧ := by rfl

end Denote

end InstArr
