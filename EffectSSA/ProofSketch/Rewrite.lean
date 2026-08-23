module

public import EffectSSA.ProofSketch.ProofSketch

/-!
# Rewrite

This file defines an `n`-ary rewrite as a pair of `n`-ary patterns, as well as:
* `Rewrite.IsSound`, a local soundness condition
-/

namespace EffectSSA.ProofSketch
public section
variable [SSA ι σ ν]

/-!
## Rewrite
-/

/--
An `n`-ary rewrite consists of a pair `(S, T)` of (well-behaved) `n`-ary patterns.
-/
structure Rewrite (ι) [SSA ι σ ν] (n : Nat) where
  src : Pattern ι n
  tgt : Pattern ι n
  wellbehaved_src : src.HasEqn
  wellbehaved_tgt : tgt.HasEqn

namespace Rewrite

attribute [simp, grind .] Rewrite.wellbehaved_src Rewrite.wellbehaved_tgt

/--
A rewrite is sound when its source is refined by its target.
-/
abbrev IsSound (rw : Rewrite ι n) : Prop :=
  rw.src.DenRefine rw.tgt

/--
Show that `is` is refined by `js` by relating these programs to
some (complete) multi-context `C` via the given (sound) rewrite `rw`.
-/
theorem isRefinedBy_of_contextual_isRefinedBy (rw : Rewrite ι n) (h : rw.IsSound)
    (is js : InstSeq ι) (his : is.WellFormed ∅) (hjs : js.WellFormed ∅) :
    (∃ C : MultiContext ι n, C.Complete ∧
      is = C.plug rw.src ∧ js = C.plug rw.tgt)
    → ⟦is⟧ {} ⊒ ⟦js⟧ {} := by
  rintro ⟨C, hC, h₁, h₂⟩
  rw [h₁, h₂]
  apply Pattern.ctxRefine_of_denoteRefine
  <;> grind

end Rewrite

/-!
## toContext
-/

namespace Inst

/--
`i.toHole? xs` returns a hole with index `h`,
with `xs[h]` is equal to `i.results`,
or the original context instruction unchanged if no such index exists.
-/
@[expose] def toHole (xs : List (List VarId)) [NeZero xs.length]
    (i : Inst ι) : Inst ι ⊕ Hole xs.length :=
  match xs.idxOf? i.results with
  | some idx => .inr <| Fin.ofNat _ idx
  | none => .inl i

variable {xs : List (List VarId)} {ne : NeZero xs.length}

@[simp, grind =]
theorem toHole_eq_inl_iff (i j : Inst ι) :
    i.toHole xs = .inl j ↔ j = i ∧ i.results ∉ xs := by
  grind [Inst.toHole]

@[simp, grind =]
theorem toHole_eq_inr_iff (i : Inst ι) (h : Hole xs.length) :
    (i.toHole xs = Sum.inr h) ↔ List.idxOf? i.results xs = some h.val := by
  unfold Inst.toHole; split
  next _ idx heq =>
    simp only [Sum.inr.injEq, heq, Option.some.injEq]
    have hlt : idx < xs.length := by grind [List.idxOf?_eq_some_iff]
    constructor <;> rintro rfl <;> simp [Nat.mod_eq_of_lt hlt]
  next => grind

end Inst

namespace InstSeq

/--
`is.toContext xs` returns a multi-context derived from `is` by replacing
each instruction `i` whose list of results is an element in `xs` with a hole
of the corresponding index (and leaving other instructions as-is).

Note: `n` ought to be at least the size of `xs`, or
the hole indices will get wrapped.
-/
@[expose] def toContext (xs : List (List VarId)) [NeZero xs.length] :
    InstSeq ι → MultiContext ι xs.length :=
  List.map (Inst.toHole xs)

variable {xs : List (List VarId)} [NeZero xs.length]

@[simp, grind =] theorem toContext_append (is js : InstSeq ι) :
    (is ++ js).toContext xs = is.toContext xs ++ js.toContext xs := by
  simp [toContext]

@[simp, grind =] theorem toContext_singleton (i : Inst ι) :
    toContext xs [i] = [i.toHole xs] := rfl

/--
A context derived from sequence `is` via result variables `xs` is complete iff:
* `xs` contains no duplicate elements, and
* for each list of results `x ∈ xs`, there is some instruction `i ∈ is`
  which defines those variables.
-/
theorem complete_toContext_iff (is : InstSeq ι) :
    (is.toContext xs).Complete ↔
      xs.Pairwise (· ≠ ·)
      ∧ ∀ x ∈ xs, ∃ i ∈ is, i.results = x := by
  simp only [MultiContext.Complete, InstSeq.toContext, List.mem_map, Inst.toHole_eq_inr_iff, ne_eq]
  constructor
  · intro h
    and_intros
    · rw [List.pairwise_iff_getElem]
      intro i j hi hj hij heq
      have := h ⟨i, hi⟩
      have := h ⟨j, hj⟩
      grind [List.idxOf?_eq_some_iff]
    · intro x hx
      obtain ⟨idx, hidx, rfl⟩ : ∃ idx, ∃ h : idx < xs.length, xs[idx] = x :=
        List.getElem_of_mem hx
      specialize h ⟨idx, hidx⟩
      obtain ⟨i, hi, hmatch⟩ := h
      exists i, hi
      grind [List.idxOf?_eq_some_iff]
  · intro ⟨hd, h⟩ hole
    specialize h (xs[hole.val]) (by grind)
    obtain ⟨i, hi, hres⟩ := h
    exists i, hi
    cases h : xs.idxOf? i.results
    case none => grind
    case some idx =>
      suffices idx = hole.val by simpa
      have : ∃ h : idx < xs.length, xs[idx] = xs[hole.val] := by
        grind [List.idxOf?_eq_some_iff]
      suffices ¬(idx < hole.val) ∧ ¬(hole.val < idx) by grind
      grind [List.pairwise_iff_getElem]

variable (xs) in
theorem plug_toContext_eq_self_of (is : InstSeq ι) (I : Pattern ι xs.length) :
    (∀ i ∈ is, ∀ idx, ∀ (_ : idx < xs.length),
        xs.idxOf? i.results = some idx → I[idx] = [i])
    → (is.toContext xs).plug I = is := by
  intro h
  simp only [MultiContext.plug, Pattern.getElem_hole, toContext, List.flatMap_map]
  induction is
  case nil => simp
  case cons i is ih =>
    specialize ih <| by grind
    specialize h i (by grind)
    grind
