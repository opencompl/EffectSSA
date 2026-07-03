import EffectSSA.Assumptions.LawfulMemoryModel
import EffectSSA.Upstream.List

import EffectSSA.Trace.Defs
import EffectSSA.Trace.Compat

/-!
# Split & Merge Operations
-/
namespace EffectSSA
variable {τ : Ty} [LawfulMemoryModel τ]

noncomputable section

namespace Trace

attribute [local simp] List.pairwise_map

/-!
## Split
-/

/--
Split a single trace into two, by splitting the clock value, while duplicating
all events.
-/
def split (es : Trace τ) : Trace τ × Trace τ :=
  ( { es with
        clock  := es.clock.split.fst
        events := es.events.map .cast_le
        compat := by simpa using es.compat },
    { es with
        clock  := es.clock.split.snd
        events := es.events.map .cast_le
        compat := by simpa using es.compat }
    )

/-!
## Merge
-/
section Merge

/--
`dedup xs ys` deduplicates events across two bare traces (i.e. lists of clocked
events), returning a list of all events in `ys` which were not present (with
the same clock value!) in `xs`.
-/
def dedup {c} (es : List (ClockedEvent τ c)) : List (ClockedEvent τ c) → List (ClockedEvent τ c) :=
  List.filter (· ∈ es)

def mergeEvents {c} : List (ClockedEvent τ c) → List (ClockedEvent τ c) → List (ClockedEvent τ c)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x.clock ≤ y.clock then
        y :: (mergeEvents (x :: xs) ys)
      else
        x :: (mergeEvents xs (y :: ys))

section Lemmas
variable {c} {es₁ es₂ : List (ClockedEvent τ c)}

@[simp, grind =] theorem mem_mergeEvents : e ∈ mergeEvents es₁ es₂ ↔ (e ∈ es₁ ∨ e ∈ es₂) := by
  fun_induction mergeEvents <;> grind

@[grind! .] theorem compat_mergeEvents
    (hc : ∀ e₁ ∈ es₁, ∀ e₂ ∈ es₂, e₁ ⌣ e₂)
    (h₁ : es₁.Pairwise (· ⌣ ·)) (h₂ : es₂.Pairwise (· ⌣ ·)) :
    (mergeEvents es₁ es₂).Pairwise (· ⌣ ·) := by
  fun_induction mergeEvents
  · grind
  · grind
  case case3 ih =>
    specialize ih (by grind) (by grind) (by grind)
    simp only [List.pairwise_cons, mem_mergeEvents, List.mem_cons, ih, and_true]
    intro e h
    rcases h with ((_|_)|_)
    · grind
    · apply ClockedEvent.compat_symm
      grind
    · simp at h₁ h₂; grind
  case case4 ih =>
    specialize ih (by grind) (by grind) (by grind)
    simp only [List.pairwise_cons, mem_mergeEvents, List.mem_cons, ih, and_true]
    rintro e (_|rfl|_)
    · simp at h₁; grind
    · grind
    · grind

@[grind .] theorem compat_dedup (h : es₂.Pairwise (· ⌣ ·)) : (dedup es₁ es₂).Pairwise (· ⌣ ·) := by
  induction es₂ <;> simp [dedup]; grind

@[grind .] theorem compat_of_mem_dedup {e₁ e₂} (h₂ : e₂ ∈ dedup es₁ es₂) (h₁ : e₁ ∈ es₁)
    (h : es₁.Pairwise (· ⌣ ·)) : e₁ ⌣ e₂ := by
  unfold dedup at h₂
  fun_induction List.filter
  case case1 => contradiction
  case case2 y es₂ hy ih =>
    replace hy : y ∈ es₁ := by grind
    replace h₂ : e₂ = y ∨ e₂ ∈ es₂ ∧ e₂ ∈ es₁ := by grind
    rcases h₂ with (h₂|h₂)
    · subst h₂
      apply List.rel_of_pairwise <;> assumption
    · rcases h₂
      apply List.rel_of_pairwise <;> assumption
  case case3 => grind

end Lemmas

def merge (es₁ : Trace τ) (es₂ : Trace τ) : Trace τ :=
  let clock := es₁.clock.merge es₂.clock
  let events₁ := es₁.events.map (.cast_le (c' := clock) (by grind))
  let events₂ := es₂.events.map (.cast_le (c' := clock) (by grind))
  if h : es₁.isUB ∨ es₂.isUB ∨ ¬(es₁ ⌣ es₂) then
    .ub
  else
    let events := mergeEvents events₁ (dedup events₁ events₂)
    { clock, events, isUB := false,
      compat := by
        have hp₁ := es₁.compat (by grind)
        have hp₂ := es₂.compat (by grind)
        rintro -
        apply compat_mergeEvents
        · intros e₁ he₁ e₂ he₂
          refine compat_of_mem_dedup he₂ he₁ ?_
          show (es₁.events.map _).Pairwise _
          simpa using hp₁
        · show (es₁.events.map _).Pairwise _
          simpa using hp₁
        · apply compat_dedup
          show (es₂.events.map _).Pairwise _
          simpa using hp₂
    }
where
