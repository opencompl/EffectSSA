module

public import EffectSSA.ProofSketch.Notation.Refinement
public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.InstSeq
public import EffectSSA.ProofSketch.Pattern
public import EffectSSA.ProofSketch.MultiContext
public import EffectSSA.ProofSketch.Effect
public import EffectSSA.ProofSketch.CFG
public import EffectSSA.ProofSketch.Assumptions

/-!
# Contextual Equivalence Proof Sketch

This file contains a stand-alone proof sketch that denotational equivalence
implies contextual equivalence, in an SSA-based rewriting setting.

-/

@[expose] public noncomputable section
namespace EffectSSA.ProofSketch

/-!
## Semantics
-/
section Semantics
variable [SSA ι σ ν]

/-! ### Definition -/

structure LocalEnv (ι) {σ ν} [SSA ι σ ν] : Type where
  get? : VarId → Option ν := fun _ => none

instance : CoeFun (LocalEnv ι) (fun _ => VarId → Option ν) where
  coe := LocalEnv.get?

/--
A stateful environment `e : SEnv`
bundles a pure environment with a global state.
-/
structure SEnv (ι) {σ ν} [ssa : SSA ι σ ν] : Type where
  /-- A partial map from local variables (i.e, virtual registers) to values. -/
  locals : LocalEnv ι := { }
  /-- The global state, e.g, for memory and UB -/
  state : σ := ssa.initialState
  /-- Whether an interpretation occurred (indicating a mallformed program). -/
  error : Bool := false


/-! ### LocalEnv-/
namespace LocalEnv

/--
`ℓ.with? xs vs` returns the local environment `ℓ` with each variable `xs[i]`
set to the corresponding value `vs[i]`,
returining `none` if `xs` and `vs` are of different lengths.
-/
def with? (ℓ : LocalEnv ι) (xs : List VarId) (vs : List ν) : Option (LocalEnv ι) :=
  if xs.length != vs.length then
    none
  else
    some { get? x :=
      match xs.idxOf? x with
      | some idx => vs[idx]?
      | none => ℓ x
    }

def «with» (ℓ : LocalEnv ι) (x : VarId) (v : ν) : LocalEnv ι where
  get? y := if x = y then v else ℓ y

section Lemmas
variable (ℓ : LocalEnv ι)

@[ext, grind ext]
theorem ext {ℓ κ : LocalEnv ι} (h : ∀ x, ℓ x = κ x) : ℓ = κ := by
  cases ℓ; cases κ; congr; funext x; apply h x

@[simp, grind =]
theorem with?_cons_cons : ℓ.with? (x :: xs) (v :: vs) = (·.with x v) <$> ℓ.with? xs vs := by
  simp only [with?, List.length_cons, Nat.reduceBneDiff, bne_iff_ne, ne_eq, ite_not]
  by_cases hl : xs.length = vs.length
  case neg => grind
  case pos =>
    simp only [hl, ↓reduceIte, Option.map_eq_map, Option.map_some, Option.some.injEq]
    congr 1; funext y
    grind

@[simp, grind =]
theorem with?_nil_nil : ℓ.with? [] [] = some ℓ := by
  simp [with?]

@[simp, grind =] theorem get?_with :
    (ℓ.with x v).get? y = if x = y then some v else ℓ y := by rfl


end Lemmas
end LocalEnv

/-! ### Denotation  -/

/--
`getD (some ρ)` returns `ρ`, `getD none` returns a default environment
with the `error` flag set. -/
abbrev SEnv.getD : Option (SEnv ι) → SEnv ι :=
  (Option.getD · { error := true})

/--
The denotation of an `Inst`struction looks up the values of the declared
arguments from the context `ρ`, then passes it to the denotation of the
contained `opCode`, and updates the environment with the resulting values.
-/
instance : Denote (Inst ι) (SEnv ι → SEnv ι) where
  denote i ρ := SEnv.getD <| do
    let args ← i.args.mapM ρ.locals
    let (state, results) := ⟦i.opCode⟧ ρ.state args
    let locals ← ρ.locals.with? i.results results
    return { ρ with locals, state }
/--
An `InstSeq` is evaluated by evaluating each instruction in turn,
threading the environment through.
-/
@[default_instance]
instance : Denote (InstSeq ι) (SEnv ι → SEnv ι) where
  denote is := is.foldl (fun (ρ : SEnv ι) i => ⟦i⟧ ρ)

/--
A `Pattern` is evaluated by collapsing it into an instruction sequence,
and evaluating that.
-/
instance : Denote (Pattern ι n) (SEnv ι → SEnv ι) where
  denote I := ⟦I.collapse⟧

/-! ### Properties -/
section Properties

theorem Inst.denote_eq {i : Inst ι} :
    ⟦i⟧ ρ =
      let ρ? : Option (SEnv ι) := do
        let args ← i.args.mapM ρ.locals
        let (state, results) := ⟦i.opCode⟧ ρ.state args
        let locals ← ρ.locals.with? i.results results
        return { ρ with locals, state }
      ρ?.getD { error := true } := by rfl

theorem InstSeq.denote_eq {is : InstSeq ι} :
    ⟦is⟧ = is.foldl (fun (ρ : SEnv ι) i => ⟦i⟧ ρ) := by rfl

@[simp, grind =] theorem InstSeq.denote_nil : ⟦([] : InstSeq ι)⟧ = (id : SEnv ι → SEnv ι) := by rfl
@[simp, grind =] theorem InstSeq.denote_nil_apply (ρ : SEnv ι) : ⟦([] : InstSeq ι)⟧ ρ = ρ := by rfl

@[simp, grind =] theorem InstSeq.denote_cons {i : Inst ι} {is : InstSeq ι} :
    ⟦i ;> is⟧ = fun (ρ : SEnv ι) => ⟦is⟧ (⟦i⟧ ρ) := by rfl

@[simp, grind =] theorem InstSeq.denote_append (is js : InstSeq ι) :
    ⟦is ++ js⟧ = fun ρ => ⟦js⟧ (⟦is⟧ ρ) := by
  grind [InstSeq.denote_eq]


@[grind =] theorem Pattern.denote_eq {I : Pattern ι n} :
    ⟦I⟧ = ⟦I.collapse⟧ := by rfl

@[simp, grind =] theorem Pattern.denote_nil {I : Pattern ι 0} : ⟦I⟧ = id := by
  cases I; rfl

@[simp, grind =]
theorem Pattern.denote_cons  (is : InstSeq ι) (I : Pattern ι n) :
    ⟦cons is I⟧ = fun ρ => ⟦I⟧ (⟦is⟧ ρ) := by
  simp [Pattern.denote_eq]

/-! results -/
variable {x : VarId}

/-- Instructions only modify the registers in their `results` set. -/
@[grind .] axiom Inst.locals_denote_of_not_mem_results (i : Inst ι) {x : VarId} {ρ : SEnv ι}
    (h : x ∉ i.results) : (⟦i⟧ ρ).locals x = ρ.locals x
  -- TODO: ^^ this result should now be provable

@[grind =] theorem InstSeq.locals_denote_of_not_mem_results {is : InstSeq ι} {ρ : SEnv ι}
    (h : x ∉ is.results) :
    (⟦is⟧ ρ).locals x = ρ.locals x := by
  induction is generalizing ρ <;> grind

end Properties

/-! #### MultiContext Semantics -/

/-- `HoleEnv ι n` is the type of a substitution mapping holes to instruction sequences. -/
abbrev HoleEnv (ι) (n : Nat) := Hole n → InstSeq ι

namespace MultiContext
variable (C : MultiContext ι n)

instance : Denote (MultiContext ι n) (HoleEnv ι n → SEnv ι → SEnv ι) where
  denote C η := C.foldl <| fun (ρ : SEnv ι) i =>
                  match i with
                  | .inl (i : Inst ι) => ⟦i⟧ ρ
                  | .inr (h : Hole n) => ⟦η h⟧ ρ

theorem denote_eq : ⟦C⟧ = fun (η : HoleEnv ι n) => C.foldl (fun (ρ : SEnv ι) i =>
                                      match i with
                                      | .inl (i : Inst ι) => ⟦i⟧ ρ
                                      | .inr (h : Hole n) => ⟦η h⟧ ρ) := rfl

@[simp, grind =]
theorem denote_nil' : ⟦([] : MultiContext ι n)⟧ η = (id : SEnv ι → SEnv ι) := rfl

@[simp, grind =] theorem denote_cons_inst' (i : Inst ι) :
    ⟦(Sum.inl i :: C : MultiContext ι n)⟧ = fun η ρ => ⟦C⟧ η (⟦i⟧ ρ) := by rfl

@[simp, grind =] theorem denote_cons_hole' (h : Hole n) :
    ⟦(Sum.inr h :: C : MultiContext ι n)⟧ = fun η ρ => ⟦C⟧ η (⟦η h⟧ ρ) := by rfl

@[simp, grind =]
theorem denote_plug : ⟦C.plug I⟧ = ⟦C⟧ (I[·]) := by
  funext ρ
  induction C generalizing ρ
  case nil => simp
  case cons i C ih => cases i <;> grind

end MultiContext
end Semantics

variable [SSA ι σ ν]

/-!
## Refinement
-/
section Refine

/--
We say that `ρ` is a sub-environment of `η`, written as `ρ ⊒ η`,

* the global state of `ρ` is refined by the global state of `η`, and
* for each variable `v` in the domain of `ρ`,
    the value `ρ v` is refined by `η v`.
-/
instance : Refinement (SEnv ι) where
  IsRefinedBy ρ η := !ρ.error →
    !η.error ∧ ρ.state ⊒ η.state ∧ (∀ v, ρ.locals v ⊒ η.locals v)

section RefineLemmas
variable {ρ η : SEnv ι}

@[grind =]
theorem SEnv.isRefinedBy_iff : ρ ⊒ η ↔ !ρ.error →
    !η.error ∧ ρ.state ⊒ η.state ∧ (∀ v, ρ.locals v ⊒ η.locals v) := by rfl

@[simp, grind =>]
theorem SEnv.isRefinedBy_of_error :
    ρ.error → ρ ⊒ η := by
  simp [(· ⊒ ·)]; grind

@[simp, grind =>]
theorem SEnv.isRefinedBy_iff_of_error_right {ρ η : SEnv ι} :
    η.error → (ρ ⊒ η ↔ ρ.error) := by
  simp [(· ⊒ ·)]; grind

/-! #### Congruence Lemmas -/
section RefineCongr

/--
Each instruction's semantics preserves refinement.
In other words, the semantics are *monotone* w.r.t. the refinement relation.
-/
@[grind .] axiom Inst.denote_isRefinedBy_congr {ρ₁ ρ₂ : SEnv ι} (hρ : ρ₁ ⊒ ρ₂) (i : Inst ι) :
    ⟦i⟧ ρ₁ ⊒ ⟦i⟧ ρ₂

@[grind .] theorem InstSeq.denote_isRefinedBy_congr {ρ₁ ρ₂ : SEnv ι} (hρ : ρ₁ ⊒ ρ₂) (is : InstSeq ι) :
    ⟦is⟧ ρ₁ ⊒ ⟦is⟧ ρ₂ := by
  induction is generalizing ρ₁ ρ₂
  · simpa
  · grind

@[grind .] theorem Pattern.denote_isRefinedBy_congr {ρ₁ ρ₂ : SEnv ι} (hρ : ρ₁ ⊒ ρ₂) (I : Pattern ι n) :
    ⟦I⟧ ρ₁ ⊒ ⟦I⟧ ρ₂ := by
  simp [Pattern.denote_eq, InstSeq.denote_isRefinedBy_congr hρ]

end RefineCongr
end RefineLemmas
end Refine

/-!
## Equation Lemma
-/
section EqnLemma

def Inst.EqnLemma (i : Inst ι) (x : VarId) (ρ : SEnv ι) : Prop :=
  x ∈ i.results → (⟦i⟧ ρ).locals x = ρ.locals x

@[grind] def InstSeq.EqnLemma (is : InstSeq ι) (x : VarId) (ρ : SEnv ι) : Prop :=
  ∀ i ∈ is, Inst.EqnLemma i x ρ

@[grind] def Pattern.EqnLemma (I : Pattern ι n) (x : VarId) (ρ : SEnv ι) : Prop :=
  ∀ i ∈ I, InstSeq.EqnLemma i x ρ

-- TODO: HasEqn should probably be called WellBehaved or some such

/--
We say that an instruction `i` has a well-behaved equation lemma when:

* validity of the equation lemma is stable under the execution of more instructions, and
* executing `i` is guaranteed to yield an environment that satisfies its
  own equation lemma
-/
structure Inst.HasEqn (i : Inst ι) : Prop where
  stable : ∀ x ρ, Inst.EqnLemma i x ρ → ∀ j : Inst ι, x ∉ j.results → Inst.EqnLemma i x (⟦j⟧ ρ)
  idempotent : ∀ x ρ, Inst.EqnLemma i x (⟦i⟧ ρ)

@[grind] def InstSeq.HasEqn (is : InstSeq ι) : Prop :=
  ∀ i ∈ is, Inst.HasEqn i

@[grind] def Pattern.HasEqn (I : Pattern ι n) : Prop :=
  ∀ i ∈ I, InstSeq.HasEqn i

section Lemmas
variable {i : Inst ι} {is : InstSeq ι} {I : Pattern ι n}

/-! vacuous -/

@[grind =>] theorem Inst.eqnLemma_of_not_mem_results {ρ : SEnv ι} (hx : x ∉ i.results) :
    EqnLemma i x ρ := by
  grind [EqnLemma]

@[grind =>] theorem InstSeq.eqnLemma_of_not_mem_results {ρ : SEnv ι} (hx : x ∉ is.results) :
    EqnLemma is x ρ := by
  intro i hi
  grind

@[grind =>] theorem Pattern.eqnLemma_of_not_mem_results {ρ : SEnv ι} (hx : x ∉ I.results) :
    EqnLemma I x ρ := by
  intro is his
  grind

/-! structural lemmas -/
variable (I : Pattern ι n) (is : InstSeq ι)

@[simp, grind .] theorem InstSeq.EqnLemma_nil {ρ : SEnv ι} :
    InstSeq.EqnLemma ([] : InstSeq ι) x ρ := by
  grind [InstSeq.EqnLemma]

@[simp, grind =] theorem InstSeq.EqnLemma_cons {i : Inst ι} {is : InstSeq ι} {ρ : SEnv ι} :
    InstSeq.EqnLemma (i ;> is) x ρ ↔ Inst.EqnLemma i x ρ ∧ InstSeq.EqnLemma is x ρ := by
  grind [InstSeq.EqnLemma]

variable {I} in
@[grind .]
theorem Pattern.eqnLemma_of_mem_results_get {k : Nat} {hk} {ρ : SEnv ι}
    (hx : x ∈ I[k].results) (wf : I.NoShadowing):
    Pattern.EqnLemma I x ρ ↔ InstSeq.EqnLemma I[k] x ρ := by
  generalize hi : I[k] = is
  constructor
  · grind
  · intro h js hj
    by_cases is = js; grind
    by_cases x ∈ is.results
    · have : x ∉ js.results := by
        have := results_disjoint_of_mem_of_noShadowing (by grind : is ∈ I) hj
        grind
      grind
    · grind

/-! stability -/

attribute [grind =>] Inst.HasEqn.stable

/--
If `is.HasEqn`, then validity of the equation lemma is stable under the execution
another instruction `j`.
-/
@[grind =>]
theorem InstSeq.eqnLemma_of_eqnLemma_inst {ρ : SEnv ι} (hEqn : HasEqn is) :
    EqnLemma is x ρ → ∀ j : Inst ι, x ∉ j.results → EqnLemma is x (⟦j⟧ ρ) := by
  grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another instruction `j`.
-/
@[grind =>]
theorem Pattern.eqnLemma_of_eqnLemma_inst {ρ : SEnv ι} (hEqn : HasEqn I) :
    EqnLemma I x ρ → ∀ j : Inst ι, x ∉ j.results → EqnLemma I x (⟦j⟧ ρ) := by
  grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Pattern.eqnLemma_of_eqnLemma_instSeq {ρ : SEnv ι} (hI : HasEqn I) :
    EqnLemma I x ρ → ∀ js : InstSeq ι, x ∉ js.results → EqnLemma I x (⟦js⟧ ρ) := by
  intro heqn js hjs
  induction js generalizing ρ
  · exact heqn
  · grind

/--
If `i.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Inst.eqnLemma_of_eqnLemma_instSeq {i : Inst ι} {ρ : SEnv ι} (hi : HasEqn i) :
    EqnLemma i x ρ → ∀ js : InstSeq ι, x ∉ js.results → EqnLemma i x (⟦js⟧ ρ) := by
  intro heqn js hjs
  induction js generalizing ρ
  · exact heqn
  · grind

/-! denote lemmas -/

@[grind =] theorem Inst.locals_denote_of_eqnLemma {i : Inst ι} {ρ : SEnv ι}
    (h : EqnLemma i x ρ) : (⟦i⟧ ρ).locals x = ρ.locals x := by
  grind [EqnLemma]

@[grind .] theorem InstSeq.locals_denote_of_eqnLemma {is : InstSeq ι} {ρ : SEnv ι}
    (hEqn : HasEqn is)
    (hwf : is.NoShadowing) (h : EqnLemma is x ρ) :
    (⟦is⟧ ρ).locals x = ρ.locals x := by
  induction is generalizing ρ
  · rfl
  · grind

/-! idempotence -/

attribute [grind .] Inst.HasEqn.idempotent

/--
If `is.HasEqn`, then evaluating `is` is guaranteed to yield an environment which
satisfies its own equation lemma at any variable.
-/
@[grind =>]
theorem InstSeq.eqnLemma_denote_self {is : InstSeq ι} (hEqn : HasEqn is)
    (hwf : is.NoShadowing) (ρ) :
    EqnLemma is x (⟦is⟧ ρ) := by
  induction is generalizing ρ
  · simp
  · simp; grind

end Lemmas

section EqnLemmaUpTo

/--
`I.usesAt v` is an alias of `I.collapse.usesAt v`.

See `InstSeq.usesAt` for details.
-/
abbrev Pattern.usesAt (v : VarId) (I : Pattern ι n) := I.collapse.usesAt v

/--
`I.getDef? v` is an alias of `I.collapse.getDef? v`.

See `InstSeq.getDef?` for details.
-/
abbrev Pattern.getDef? (v : VarId) (I : Pattern ι n) :=
  I.collapse.getDef? v

/--
`I.EqnLemmaUpTo h ρ` holds when `ρ` satisfies the equation lemma for all
(transitive) dependencies of the `h`-th pattern of `I`.
-/
def Pattern.EqnLemmaUpTo (I : Pattern ι n) (h : Hole n) (ρ : SEnv ι) : Prop :=
  ∀ x ∈ I[h].args,
    ∀ y, y = x ∨ y ∈ (I.usesAt x) → Pattern.EqnLemma I y ρ

end EqnLemmaUpTo
end EqnLemma

/-!
## Denotational Refinement & Equivalence
-/
section Denotational

/--
A pattern `I` is denotationally refined by pattern `J`,
when for any hole `h` and environments such that `ρ ⊒ η` and
`ρ` (resp `η`) satisfies the equation lemma for all (transitive) dependencies
of the `h`-th sequence of `I` (resp `J`), it is the case that the denotation of
`h`-th of `I` under `ρ` is refined by the denotation of the `h`-th hole of `J`
under `η`.

TODO: We ought to prove that this condition is actually implied by the much more
simple `⟦I⟧ ρ ⊒ ⟦J⟧ ρ` with some side-condition on the variables of each pattern
in `I` and `J`.
-/
def Pattern.DenRefine (I J : Pattern ι n) : Prop :=
  ∀ h : Hole n, ∀ ρ η, ρ ⊒ η →
    I.EqnLemmaUpTo h ρ →
    J.EqnLemmaUpTo h η →
    ⟦ I[h] ⟧ ρ ⊒ ⟦ J[h] ⟧ η

-- Sanity check: we should check/proof that denrefine is at least reflexive,
-- but it likely should be a pre-order (not quite partial, because antisymmetry is
-- probably broken, but that can be fixed w/ quotients)

/--
A pattern `I` is denotationally equivalent to pattern `J`,
when for any hole `h` and environments `ρ` which satisfies the equation lemma
for all (transitive) dependencies of the `h`-th hole of both `I` and `J`,
it is the case that the denotation of `h`-th of `I` is equal to the denotation
of the `h`-th hole of `J`.
-/
def Pattern.DenEquiv (I J : Pattern ι n) : Prop :=
  ∀ h : Hole n, ∀ ρ η,
    I.EqnLemmaUpTo h ρ →
    J.EqnLemmaUpTo h η →
    ⟦ I[h] ⟧ ρ = ⟦ J[h] ⟧ η

end Denotational

/-!
## Contextual Refinement
-/

/--
A pattern `I` is contextually refined by pattern `J`,
when for any complete context `C` such that `C[I]` and `C[J]` are both
wellformed, `C[I]` is (denotationally) refined by `C[J]`.
-/
def Pattern.CtxRefine (I J : Pattern ι n) : Prop :=
  ∀ (C : MultiContext ι n), C.Complete →
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed ∅ → CJ.WellFormed ∅ →
      ⟦CI⟧ {} ⊒ ⟦CJ⟧ {}

/-!
## Residual
-/
section Residual

/--
We say that `Γ` is a residual of context `C` under pattern `I` when

TODO: dedup with Invariant
-/
@[grind, grind cases]
private structure Residual (Γ : VarSet) (C : MultiContext ι n) (I : Pattern ι n) where
  /-- `C.plug I` is well-formed with free variables `Γ`. -/
  wf : (C.plug I).WellFormed Γ
  residual : ∀ x ∈ I.results, x ∉ Γ → (∃ h, .inr h ∈ C ∧ x ∈ I[h].results)

namespace Residual
variable {Γ : VarSet} {C : MultiContext ι n} {I : Pattern ι n} {i : Inst ι} {h : Hole n}

/-! invariants -/

private theorem initial (wf : (C.plug I).WellFormed ∅) (hC : C.Complete) : Residual ∅ C I := by
  grind [Pattern.mem_iff_getElem_hole, MultiContext.Complete]

@[grind →] private theorem of_cons_inst :
    Residual Γ (.inl i :: C) I → Residual (i.resultsSet ∪ Γ) C I := by
  rintro ⟨wf, residual⟩; constructor
  · grind
  · intro x; have := residual x; grind

@[grind →] private theorem of_cons_hole  :
    Residual Γ (.inr h :: C) I → Residual (I[h].results ∪ Γ) C I := by
  rintro ⟨wf, residual⟩; constructor
  · grind
  · intro x; have := residual x; grind

end Residual
end Residual

/-!
## Main Result for straight-line programs
-/
attribute [grind =] id_eq

open MultiContext (plug)

/-! ### Invariant -/

/--
In the main proof, we will do induction on the context `C`, meaning that the
context considered in the inductive step will be a sub-context of the original
program context.

Within the proof, we will keep track of a residual variable set `Γ`, which has
all variables of the original program considered in previous steps of the
induction, thus we keep the following invariant about `Γ`.
-/
@[grind, grind cases] private structure Invariant
    (Γ : VarSet) (C : MultiContext ι n) (I : Pattern ι n) (ρ : SEnv ι)
    extends Residual Γ C I where
  /--
  If `x ∈ Γ`, then any transitive dependencies of `x` (in `I`) are also
  part of `Γ`.
  -/
  closed : ∀ x ∈ Γ, ∀ y ∈ I.usesAt x, y ∈ Γ
  eqn : ∀ x ∈ Γ, I.EqnLemma x ρ
  ns : I.NoShadowing


namespace Invariant
variable {Γ} {C : MultiContext ι n} {I : Pattern ι n} {ρ : SEnv ι} {i : Inst ι}

private theorem initial (wf : (C.plug I).WellFormed ∅) (hC : C.Complete) : Invariant ∅ C I { } := by
  have nsI : I.NoShadowing := by
    apply C.noShadowing_pattern_of_plug_noShadowing
    <;> grind
  grind [Pattern.mem_iff_getElem_hole, MultiContext.Complete]

private theorem of_invariant_cons_inst (hI : I.HasEqn := by assumption) :
    Invariant Γ (.inl i :: C) I ρ → Invariant (i.resultsSet ∪ Γ) C I (⟦i⟧ ρ) := by
  rintro ⟨residual, closed, eqn, nsI⟩
  have : ∀ x ∈ i.resultsSet, x ∉ I.results := by
    intro x hx hxI
    have : x ∉ (C.plug I).results := by grind
    obtain ⟨h, hhC, hhx⟩ : ∃ h, Sum.inr h ∈ C ∧ x ∈ I[h].results := by
      have : x ∉ Γ := by grind
      have := residual.residual x hxI;
      grind
    grind
  constructor
  <;> grind

private theorem of_invariant_cons_hole (hI : I.HasEqn := by assumption) :
    Invariant Γ (.inr h :: C) I ρ →
    Invariant (I[h].results ∪ Γ) C I (⟦I[h]⟧ ρ) := by
  rintro ⟨residual, closed, eqn, nsI⟩
  generalize his : I[h] = is at *
  constructor
  · grind
  · have hΔ : is.args ⊆ Γ := by grind
    replace his : is ⊆ I.collapse := by grind
    generalize Γ = Δ at ⊢ hΔ closed
    clear eqn
    intro x hx y hy
    induction is generalizing Δ with
    | nil => grind
    | cons i is ih =>
        have his : is ⊆ I.collapse := by grind
        have hΔ' : is.args ⊆ i.resultsSet ∪ Δ := by grind
        specialize ih his _ hΔ'
        specialize ih <| by -- prove closedness
          clear ih
          intro x hx y hy
          by_cases x ∈ Δ; grind
          have : x ∈ i.resultsSet := by grind
          · rw [InstSeq.mem_usesAt'] at hy
            obtain ⟨j, hj, hxj, hy⟩ := hy
            obtain rfl : i = j := by
              have hi : i ∈ I.collapse := by grind
              have hj : j ∈ I.collapse := by grind
              apply InstSeq.eq_of_not_disjoint_results_of_noShadowing hi hj nsI
              grind
            rcases hy with ( (hy : y ∈ i.argsSet) | ⟨z, hzi, hyz⟩ )
            · have : y ∈ Δ := by grind
              grind
            · grind
        grind
  · intro x hx
    by_cases x ∈ Γ; grind
    have hx : x ∈ is.results := by grind
    · obtain ⟨Δ, wf⟩ : ∃ Δ, is.WellFormed Δ := by grind
      subst his
      rw [Pattern.eqnLemma_of_mem_results_get hx nsI]
      apply InstSeq.eqnLemma_denote_self _
      · grind
      · grind
  · grind


end Invariant

/--
Proving denotational refinement is sufficient for showing contextual refinement.
-/
theorem Pattern.ctxRefine_of_denoteRefine (I J : Pattern ι n)
    (hI : I.HasEqn) (hJ : J.HasEqn)
    (h_denoteRefine : I.DenRefine J) :
    I.CtxRefine J := by
  intro C hC CI CJ hCI hCJ
  subst CI CJ

  suffices ∀ ρ η, ρ ⊒ η →
      ∀ {Γ}, Invariant Γ C I ρ →
      ∀ {Δ}, Invariant Δ C J η →
      ⟦C⟧ (I[·]) ρ ⊒ ⟦C⟧ (J[·]) η by
    simp only [MultiContext.denote_plug]
    apply @this { } { } ?_ ∅ ?_ ∅ ?_
    <;> grind [Invariant.initial]
  clear hC hCI hCJ

  induction C <;> (intro ρ η hρη Γ hCI Δ hCJ)
  case nil => simpa
  case cons h_or_i C ih =>
    cases h_or_i with
    | inl i =>
        apply ih (⟦i⟧ ρ) (⟦i⟧ η)
        · grind
        · apply Invariant.of_invariant_cons_inst hI hCI
        · apply Invariant.of_invariant_cons_inst hJ hCJ
    | inr h =>
        apply ih (⟦I[h]⟧ ρ) (⟦J[h]⟧ η)
        · apply h_denoteRefine
          · assumption
          · intro x (hx : x ∈ I[h].args) y hy
            have : I[h].args ⊆ Γ := by grind
            rcases hCI
            grind
          · intro x (hx : x ∈ J[h].args)
            have : J[h].args ⊆ Δ := by grind
            rcases hCJ
            grind
        · apply Invariant.of_invariant_cons_hole hI hCI
        · apply Invariant.of_invariant_cons_hole hJ hCJ
