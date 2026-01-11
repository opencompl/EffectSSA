import EffectSSA.Trace.Defs

/-!
# Trace lemmas
-/
namespace EffectSSA
variable {τ : Ty} [MemorySignature τ]

namespace Trace

/-! ## Basic constructor lemmas -/
section Basic
variable (e : Event τ) (es ds : List (Event τ))

@[simp] theorem cons_seq : e :> (seq es) = seq (e :: es) := rfl
@[simp] theorem seq_append_seq : (seq es) ++ (seq ds) = seq (es ++ ds) := rfl

end Basic


/-! ## `events` lemmas -/
theorem eq_of_mem_events {es : Trace τ} (h : z ∈ es.events) :
    es = z.pre ++ (z.event :> z.post) := by
  simp only [events, Fin.getElem_fin] at h
  split at h
  · contradiction
  · rcases z
    simp only [Set.mem_setOf_eq, TraceZipper.mk.injEq] at h
    rcases h with ⟨i, h⟩
    repeat (rcases h with ⟨rfl, h⟩)
    simp
