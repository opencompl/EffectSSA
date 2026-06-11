module

public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.Pattern

@[expose] public section
/-!
## Multi Context

We define a notion of a context with multiple holes, also called a multi-context,
by naming each hole.
-/
namespace EffectSSA.ProofSketch

/--
A `MultiContext n` is a sequence of instructions, interspersed by (named) holes, such that:

* Each hole may occur any number of times (including zero),
* There are at most `n` distinct holes
-/
abbrev MultiContext (n : Nat) := List (Inst ⊕ Hole n)

/--
A `HoleEnv n` associates each hole variable `h : Hole n` with an instruction sequence.
-/
def HoleEnv n := Hole n → InstSeq

namespace MultiContext
variable (C : MultiContext n)

/--
An `n`-ary context `C` is considered *complete* when each possible named hole `h : Hole n`
occurs at least once in `C`.
-/
abbrev Complete (C : MultiContext n) : Prop :=
  ∀ (h : Hole n), (.inr h) ∈ C

section Lemmas

@[simp] theorem complete_cons_inst : Complete (.inl i :: C) ↔ Complete C := by grind

end Lemmas


/-! ### Plugging -/
section Plug

def plug (C : MultiContext n) (I : Pattern n) : InstSeq :=
  C.flatMap <| fun i =>
    match i with
    | .inl (i : Inst) => [i]
    | .inr (h : Hole n) => I[h]

section Lemmas
variable {C}

@[simp, grind =] theorem plug_nil : plug [] I = [] := rfl

@[simp, grind =] theorem plug_cons_inst (i : Inst) :
    plug (.inl i :: C) I = i ;> plug C I := by rfl

@[simp, grind =] theorem plug_cons_hole (h : Hole n) :
    plug (.inr h :: C) I = I[h] ++ plug C I := by rfl


@[grind =] theorem mem_plug_iff (i : Inst) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ h, .inr h ∈ C ∧ i ∈ I[h] := by
  simp only [plug, List.mem_flatMap]
  constructor
  · grind
  · rintro (_ | ⟨h, _⟩ )
    · grind
    · refine ⟨.inr h, ?_⟩; grind

@[grind =] theorem mem_results_plug_iff {I : Pattern n} :
    x ∈ (C.plug I).results ↔
      (∃ i, .inl i ∈ C ∧ x ∈ i.results) ∨ (∃ h, .inr h ∈ C ∧ x ∈ (I[h]).results) := by
  grind

/-! #### Completeness -/

@[grind =] theorem mem_plug_iff_of_complete (hC : C.Complete) (i : Inst) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ (h : Hole n), i ∈ I[h] := by
  grind

/--
If context `C` is complete, then the results of pattern `I` are a subset of the
results of `C.plug I`.
-/
theorem results_subset_results_plug (hC : C.Complete) :
    I.results ⊆ (C.plug I).results := by
  grind [Pattern.mem_iff_getElem_hole]
grind_pattern results_subset_results_plug => (C.plug I).results

/-! #### WellFormedness -/

def embedPlugAux (p : I.PC) (C : MultiContext n) (hC : .inr p.hole ∈ C) : (C.plug I).PC :=
  match C with
  | .inl i :: C => (embedPlugAux p C (by grind)).succ
  | .inr h :: C =>
      if _ : h = p.hole then
        (p.pc.cast <| by grind).appendLeft
      else
        (embedPlugAux p C (by grind)).appendRight

open InstSeq (PC) in
def embedPlug (I : Pattern n) (C : MultiContext n) (hC : C.Complete) :
    I.collapse.EmbedIn (C.plug I) where
  map p :=
    let p : I.PC := .ofCollapse p
    embedPlugAux p C (by grind)
  get_map p := by
    let p' : I.PC := .ofCollapse p
    have hC' : .inr p'.hole ∈ C := by grind
    show (embedPlugAux p' C hC').get = p.get
    clear hC
    fun_induction embedPlugAux p' C hC'
    · grind
    · calc
        (p'.pc.cast ?h).appendLeft.get
        _ = (p'.pc.cast ?h).get := by grind
      · grind
      · grind
    · grind
  inj p q hpq hp hq := by
    let p' : I.PC := .ofCollapse p
    let q' : I.PC := .ofCollapse q
    have : p' ≠ q' := by grind
    have hCp : .inr p'.hole ∈ C := by grind
    have hCq : .inr q'.hole ∈ C := by grind
    show (embedPlugAux p' C hCp) ≠ (embedPlugAux q' C hCq)
    clear hC
    induction C
    case nil => grind
    case cons h_or_i C ih =>
      cases h_or_i
      case inl i => grind [embedPlugAux]
      case inr h =>
        simp only [embedPlugAux, ne_eq]
        by_cases h = p'.hole
        · by_cases hhole : p'.hole = q'.hole
          · rcases p' with ⟨hole, p'⟩
            rcases q' with ⟨_, q'⟩
            grind
          · simp only [↓reduceDIte, *]
            apply PC.appendLeft_neq_appendRight
        · by_cases h = q'.hole
          · rcases p' with ⟨phole, p'⟩
            rcases q' with ⟨qhole, q'⟩
            have : phole ≠ qhole := by grind
            have : qhole ≠ phole := by grind
            simp only [↓reduceDIte, ne_eq, *]
            intro h
            apply PC.appendLeft_neq_appendRight _ _ h.symm
          · grind

def noShadowing_pattern_of_plug_noShadowing {n} {C : MultiContext n} {I : Pattern n}
    (hC : C.Complete) :
    (C.plug I).NoShadowing → I.NoShadowing := by
  simp only [InstSeq.noShadowing_iff, ne_eq]
  intro ns i j hij
  let f := C.embedPlug I hC
  have := ns (f i) (f j)
  grind

end Lemmas
end Plug

/-!
## Conversion to `InstSeq`
-/
section Conv

def toSeq : MultiContext 0 → InstSeq :=
  List.map (fun | .inl i => i)
instance : Coe (MultiContext 0) InstSeq where coe := toSeq

def ofSeq : InstSeq → MultiContext n :=
  List.map Sum.inl
instance : Coe InstSeq (MultiContext n) where coe := ofSeq

section Lemmas

end Lemmas
end Conv
