module

public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.Pattern
public import EffectSSA.ProofSketch.Effect

public import ITreeExtras.HasEffect

@[expose] public section
/-!
## Multi Context

We define a notion of a context with multiple holes, also called a multi-context,
by naming each hole.
-/
namespace EffectSSA.ProofSketch
open ITree
open Effect (trigger)

variable {ε : Type} {κε : ε → Type} [Effect ε κε]

/--
A `MultiContext ι n` is a sequence of instructions, interspersed by (named) holes, such that:

* Each hole may occur any number of times (including zero),
* There are at most `n` distinct holes
-/
abbrev MultiContext (ι) (n : Nat) := List (Inst ι ⊕ Hole n)

/-! ### Denote -/
namespace MultiContext

/--
`C.denote` returns an `ITree` in which each instruction of the context
is represented as an `InstEff`, and each hole as a `HoleEff`.
-/
@[grind]
def denote : MultiContext ι n → ITree (HoleEff ⊕ InstEff ι) Unit
  | .inl i :: is => trigger (InstEff ι) i *> denote is
  | .inr h :: is => trigger HoleEff h.id *> denote is
  | [] => .ret ()

section DenoteLemmas

@[simp, grind =]
theorem denote_nil : denote ([] : MultiContext ι n) = .ret () := rfl

@[simp, grind =]
theorem denote_cons_inst (i : Inst ι) (C : MultiContext ι n) :
    denote (Sum.inl i :: C) = trigger (InstEff _) i *> denote C := rfl

@[simp, grind =]
theorem denote_cons_hole (h : Hole n) (C : MultiContext ι n) :
    denote (Sum.inr h :: C) = trigger HoleEff h.id *> denote C := rfl

@[simp, grind =]
theorem denote_append (C₁ C₂ : MultiContext ι n) :
    denote (C₁ ++ C₂) = C₁.denote *> C₂.denote := by
  induction C₁
  case nil => simp
  case cons h_or_i _ _ =>
    cases h_or_i <;> simp [*, seqRight_eq_bind]

end DenoteLemmas
end MultiContext

namespace MultiContext
variable (C : MultiContext ι n)

/-! ### Completeness -/
section Complete

/--
An `n`-ary context `C` is considered *complete* when each possible named hole `h : Hole n`
occurs at least once in `C`.
-/
def Complete (C : MultiContext ι n) : Prop :=
  ∀ (h : Hole n), (.inr h) ∈ C

section Lemmas

@[simp] theorem complete_cons_inst : Complete (.inl i :: C) ↔ Complete C := by
  grind [Complete]

end Lemmas
end Complete


/-! ### Plugging -/
section Plug
variable {C : MultiContext ι n} {I : Pattern ι n}

/--
Plug an `n`-ary pattern `I` into an `n`-ary context `C`, replacing each hole `h`
in `C` with the instruction sequence `I[h]`.
-/
def plug (C : MultiContext ι n) (I : Pattern ι n) : InstSeq ι :=
  C.flatMap <| fun i =>
    match i with
    | .inl (i : Inst ι) => [i]
    | .inr (h : Hole n) => I[h]

section Lemmas
variable {C C₁ C₂ : MultiContext ι n}

@[simp, grind =] theorem plug_nil : plug [] I = [] := rfl

@[simp, grind =] theorem plug_cons_inst (i : Inst ι) :
    plug (.inl i :: C) I = i :: plug C I := rfl

@[simp, grind =] theorem plug_cons_hole (h : Hole n) :
    plug (.inr h :: C) I = I[h] ++ plug C I := rfl

@[simp, grind =] theorem plug_append :
    plug (C₁ ++ C₂) I = plug C₁ I ++ plug C₂ I := by
  simp [plug, List.flatMap_append]

@[grind =] theorem mem_plug_iff (i : Inst ι) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ h, .inr h ∈ C ∧ i ∈ I[h] := by
  simp only [plug, List.mem_flatMap]
  constructor
  · grind
  · rintro (_ | ⟨h, _⟩ )
    · grind
    · refine ⟨.inr h, ?_⟩; grind

@[grind =] theorem mem_results_plug_iff {I : Pattern ι n} :
    x ∈ (C.plug I).results ↔
      (∃ i, .inl i ∈ C ∧ x ∈ i.resultsSet) ∨ (∃ h, .inr h ∈ C ∧ x ∈ (I[h]).results) := by
  grind

/-! #### Completeness -/

@[grind =] theorem mem_plug_iff_of_complete (hC : C.Complete) (i : Inst ι) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ (h : Hole n), i ∈ I[h] := by
  grind [Complete]

/--
If context `C` is complete, then the results of pattern `I` are a subset of the
results of `C.plug I`.
-/
theorem results_subset_results_plug (hC : C.Complete) :
    I.results ⊆ (C.plug I).results := by
  grind [Pattern.mem_iff_getElem_hole]
grind_pattern results_subset_results_plug => (C.plug I).results

/-! #### WellFormedness -/

def embedPlugAux (p : I.PC) (C : MultiContext ι n) (hC : .inr p.hole ∈ C) : (C.plug I).PC :=
  match C with
  | .inl i :: C => (embedPlugAux p C (by grind)).succ
  | .inr h :: C =>
      if _ : h = p.hole then
        (p.pc.cast <| by grind).appendLeft
      else
        (embedPlugAux p C (by grind)).appendRight

open InstSeq (PC) in
def embedPlug (I : Pattern ι n) (C : MultiContext ι n) (hC : C.Complete) :
    I.collapse.EmbedIn (C.plug I) where
  map p :=
    let p : I.PC := .ofCollapse p
    embedPlugAux p C (by grind [Complete])
  get_map p := by
    let p' : I.PC := .ofCollapse p
    have hC' : .inr p'.hole ∈ C := by grind [Complete]
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
    have hCp : .inr p'.hole ∈ C := by grind [Complete]
    have hCq : .inr q'.hole ∈ C := by grind [Complete]
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

def noShadowing_pattern_of_plug_noShadowing {n} {C : MultiContext ι n} {I : Pattern ι n}
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
## Conversion to/from `InstSeq`
-/
section Conv

/--
A nullary context is just a sequence of instructions.
-/
def toSeq : MultiContext ι 0 → InstSeq ι :=
  List.map (fun | .inl i => i)
instance : Coe (MultiContext ι 0) (InstSeq ι) where coe := toSeq

/--
`ofSeq is` interprets an instruction sequence `is` as a context,
of arbitrary arity `n`, which happens to not have any holes.
-/
def ofSeq : InstSeq ι → MultiContext ι n :=
  List.map Sum.inl
instance : Coe (InstSeq ι) (MultiContext ι n) where coe := ofSeq

end Conv
