module

public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.Language
public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.InstSeq
public import EffectSSA.ProofSketch.Pattern

/-!
# Contextual Equivalence Proof Sketch

This file contains a stand-alone proof sketch that denotational equivalence
implies contextual equivalence, in an SSA-based rewriting setting.

-/

@[expose] public noncomputable section
namespace EffectSSA.ProofSketch

variable {ι Var Val State} [Language ι Var Val State]
open Language (iArgs iResults)

/-!
## Semantics
-/
section Semantics

/--
An `InstSeq` is evaluated by evaluating each instruction in turn,
threading the environment through.
-/
@[default_instance]
instance : Denote (InstSeq ι) (Env ι → Env ι) where
  denote is := is.foldl (fun e i => ⟦i⟧ e)

/--
A `Pattern` is evaluated by collapsing it into an instruction sequence,
and evaluating that.
-/
instance : Denote (Pattern ι n) (Env ι → Env ι) where
  denote I := ⟦I.collapse⟧

/-! ### Properties -/
section Properties

theorem InstSeq.denote_eq {is : InstSeq ι} :
    ⟦is⟧ = is.foldl (fun e (i : ι) => ⟦i⟧ e) := by rfl

@[simp, grind =] theorem InstSeq.denote_nil : ⟦([] : InstSeq ι)⟧ = id := by rfl
@[simp, grind =] theorem InstSeq.denote_nil_apply : ⟦([] : InstSeq ι)⟧ ρ = ρ := by rfl

@[simp, grind =] theorem InstSeq.denote_cons {i : ι} {is} :
    ⟦i :: is⟧ = fun ρ => ⟦is⟧ (⟦i⟧ ρ) := by rfl

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
variable {x : Var}

/-- Instructions only modify the registers in their `results` set. -/
@[grind .] axiom Inst.regs_denote_of_not_mem_results (i : ι) {x : Var} {ρ : Env ι}
    (h : x ∉ iResults i) : (⟦i⟧ ρ).regs x = ρ.regs x

@[grind =] theorem InstSeq.regs_denote_of_not_mem_results {is : InstSeq ι}
    (h : x ∉ is.results) :
    (⟦is⟧ ρ).regs x = ρ.regs x := by
  induction is generalizing ρ <;> grind

end Properties
end Semantics

/-!
## Environment Equivalence
-/
section Equiv

/-!
To simplify life, we assume that `Val` and `State` have already been quotiented
by the relevant equivalence relations, such that equality (`· = ·`) on these
types is all that we need to compare.
-/

/--
`EquivOn P ρ η` holds when environments `ρ` and `η` agree on:

* their global state,
* their error field, and
* the value assigned to each variable `v` for which `P v` holds
-/
def Env.EquivOn (P : Var → Prop) : Env ι → Env ι → Prop := fun ρ η =>
  ρ.state = η.state
  ∧ ρ.error = η.error
  ∧ (∀ v, P v → ρ.regs v = η.regs v)

/-- If two environments are equivalent on all variables, they are equal. -/
theorem Env.eq_of_equivOn {ρ η : Env ι} : EquivOn (fun _ => True) ρ η → ρ = η := by
  rcases ρ with ⟨ρ_regs, ρ_state, ρ_error⟩
  rcases η with ⟨η_regs, η_state, η_error⟩
  simp only [EquivOn]
  intro h
  have : ρ_regs = η_regs := by funext; simp_all
  simp_all

section Lemmas
attribute [local grind] Env.EquivOn

/-
TODO: axiomatise the relevant properties of equivalence on states and values,
      then use those axioms to prove the Env.equiv_foo assumptions below.
-/

@[simp, grind ., refl]
theorem Env.equivOn_refl (ρ : Env ι) : EquivOn P ρ ρ := by
  grind

theorem Env.equiv_trans {ρ₁ ρ₂ ρ₃ : Env ι} : EquivOn P ρ₁ ρ₂ → EquivOn P ρ₂ ρ₃ → EquivOn P ρ₁ ρ₃ := by
  grind

theorem Env.equiv_symm {ρ₁ ρ₂ : Env ι} : EquivOn P ρ₁ ρ₂ → EquivOn P ρ₂ ρ₁ := by grind
grind_pattern Env.equiv_symm => Env.EquivOn P ρ₁ ρ₂

end Lemmas
end Equiv

/-!
## Refinement
-/
section Refine

axiom StateRefine : State → State → Prop
instance : HasSubset State where Subset := StateRefine

axiom ValRefine : Val → Val → Prop
instance : HasSubset Val where Subset := ValRefine

@[grind, grind cases]
inductive ValRefine? : Option Val → Option Val → Prop
  | some {v₁ v₂} (h : v₁ ⊆ v₂) : ValRefine? (some v₁) (some v₂)
  | none {v?} : ValRefine? none v?
instance : HasSubset (Option Val) where
  Subset := ValRefine?

/--
We say that `ρ` is a sub-environment of `η`, written as `ρ ⊆ η`,
when `ρ` has an error, or:

* `η` is error-free,
* the global state of `ρ` is refined by the global state of `η`,
* for each variable `v` in the domain of `ρ`,
    the value `ρ v` is refined by `η v`.
-/
instance : HasSubset (Env ι) where
  Subset ρ η := ¬ρ.error →
    ¬η.error
    ∧ ρ.state ⊆ η.state
    ∧ (∀ v, ρ.regs v ⊆ η.regs v)

section RefineLemmas
variable {ρ₁ ρ₂ ρ₃ : Env ι}

@[simp, grind .]
axiom Env.refine_refl (ρ : Env ι) : ρ ⊆ ρ

axiom Env.refine_trans {ρ₁ ρ₂ ρ₃ : Env ι} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₃ → ρ₁ ⊆ ρ₃

instance : Trans (α := Env ι) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans := Env.refine_trans

@[grind →]
axiom Env.refine_antisymm {ρ₁ ρ₂ : Env ι} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₁ → ρ₁ = ρ₂

theorem Env.eq_iff_refine_refine {ρ₁ ρ₂ : Env ι} :
    ρ₁ = ρ₂ ↔ (ρ₁ ⊆ ρ₂ ∧ ρ₂ ⊆ ρ₁) := by
  grind

/-! #### Congruence Lemmas -/
section RefineCongr

/--
We assume that each instruction's semantics preserves refinement.

In other words, the semantics are *monotone* w.r.t. the refinement relation.
-/
@[grind .] axiom Inst.denote_isRefinedBy_congr (hρ : ρ₁ ⊆ ρ₂) (i : ι) :
    ⟦i⟧ ρ₁ ⊆ ⟦i⟧ ρ₂

@[grind .] theorem InstSeq.denote_isRefinedBy_congr (hρ : ρ₁ ⊆ ρ₂) (is : InstSeq ι) :
    ⟦is⟧ ρ₁ ⊆ ⟦is⟧ ρ₂ := by
  induction is generalizing ρ₁ ρ₂
  · simpa
  · grind

@[grind .] theorem Pattern.denote_isRefinedBy_congr (hρ : ρ₁ ⊆ ρ₂) (I : Pattern ι n) :
    ⟦I⟧ ρ₁ ⊆ ⟦I⟧ ρ₂ := by
  simp [Pattern.denote_eq, InstSeq.denote_isRefinedBy_congr hρ]

end RefineCongr
end RefineLemmas
end Refine

/-! ## Pattern WellFormedness -/
namespace Pattern

@[inherit_doc InstSeq.NoShadowing]
abbrev NoShadowing (I : Pattern ι n) := I.collapse.NoShadowing

@[inherit_doc InstSeq.WellFormed]
abbrev WellFormed (Γ : VarSet Var) (I : Pattern ι n) : Prop := I.collapse.WellFormed Γ

section Lemmas
variable {I : Pattern ι n}

@[simp, grind =]
theorem wellFormed_cons :
    (cons is I).WellFormed Γ ↔ is.WellFormed Γ ∧ I.WellFormed (is.results ∪ Γ) := by
  grind

theorem wellFormed_get_of_wellFormed :
    I.WellFormed Γ → ∃ Δ, (I.get k hk).WellFormed Δ := by
  induction I generalizing Γ k
  · grind
  · cases k <;> grind
grind_pattern wellFormed_get_of_wellFormed => I.WellFormed Γ, (I.get k hk).WellFormed _

/-! results -/

theorem results_disjoint_of_mem_of_noShadowing (hi : is ∈ I) (hj : js ∈ I) (wf : I.NoShadowing) :
    is ≠ js → is.results.Disjoint js.results := by
  induction I <;> grind
-- grind_pattern results_disjoint_of_mem_of_wellFormed => is ∈ I, js ∈ I, I.WellFormed
-- grind_pattern results_disjoint_of_mem_of_wellFormed => is ∈ I, js ∈ I, I.WellFormed _

end Lemmas
end Pattern

/-!
## Domination
-/
section Domination
namespace InstSeq

/--
We say that instruction `i` dominates instruction `j` in sequence `is`,
generally written as `i |>is.IDominates<| j`, when:

* `i ∈ is`
* `j ∈ is`, and
* `i` occurs *before* `j` in `is`
-/
inductive IDominates (i j : ι) : (is : InstSeq ι) → Prop where
  | head : j ∈ is → IDominates i j (i :: is)
  | cons : k ≠ i → k ≠ j → IDominates i j is → IDominates i j (k :: is)

/--
We say that variable `x` dominates instruction `j` in sequence `is`,
generally written as `x |>is.VDominates<| j`, when there is some instruction
`i` such that `x ∈ iResults i` and `i` dominates `j`
-/
abbrev VDominates (x : Var) (j : ι) (is : InstSeq ι) : Prop :=
  ∃ i, x ∈ iResults i ∧ (i |>is.IDominates<| j)

section Lemmas

@[simp, grind .] theorem iDominates_nil : ¬(IDominates i j []) := by grind [cases IDominates]

@[grind =]
theorem iDominates_cons : IDominates i j (k :: is) ↔
    if k = i then
      j ∈ is
    else
      k ≠ j ∧ IDominates i j is := by
  grind [IDominates, cases IDominates]

@[grind →] theorem mem_of_iDominates_left : IDominates i j is → i ∈ is := by
  intro h; induction h <;> grind

@[grind →] theorem mem_of_iDominates_right : IDominates i j is → j ∈ is := by
  intro h; induction h <;> grind

@[simp] theorem vDominates_cons : VDominates x j (i :: is) ↔ (x ∈ iResults i ∧ j ∈ is) ∨ (i ≠ j ∧ VDominates x j is) := by
  grind




/-! WellFormedness -/

/--
A sequence `is` is well-formed for `Γ`, when for any instruction `i ∈ is`:
*) `i` is dominated by all non-free arguments, and
*) `i` is *not* dominated by any of it's result, nor are it's result considered free
-/
theorem wellFormed_iff_dominates (is : InstSeq ι) :
  is.WellFormed Γ ↔
    ∀ i ∈ is,
      (∀ x ∈ i.args, x ∉ Γ → (x |>is.VDominates<| i))
      ∧ (∀ y ∈ iResults i, y ∉ Γ ∧ ¬(y |>is.VDominates<| i)) := by
  induction is generalizing Γ
  · grind
  · simp; grind

end Lemmas
end InstSeq
end Domination

/-!
## Equation Lemma
-/
section EqnLemma

def Inst.EqnLemma (i : ι) (x : Var) (ρ : Env ι) : Prop :=
  x ∈ iResults i → (⟦i⟧ ρ).regs x = ρ.regs x

@[grind] def InstSeq.EqnLemma (is : InstSeq ι) (x : Var) (ρ : Env ι) : Prop :=
  ∀ i ∈ is, i.EqnLemma x ρ

@[grind] def Pattern.EqnLemma (I : Pattern ι n) (x : Var) (ρ : Env ι) : Prop :=
  ∀ i ∈ I, i.EqnLemma x ρ

/--
We say that an instruction `i` has a well-behaved equation lemma when:

* validity of the equation lemma is stable under the execution of more instructions, and
* executing `i` is guaranteed to yield an environment that satisfies its
  own equation lemma
-/
structure Inst.HasEqn (i : ι) : Prop where
  stable : ∀ x ρ, i.EqnLemma x ρ → ∀ j : Inst, x ∉ j.results → i.EqnLemma x (⟦j⟧ ρ)
  idempotent : ∀ x ρ, i.EqnLemma x (⟦i⟧ ρ)

@[grind] def InstSeq.HasEqn (is : InstSeq ι) : Prop :=
  ∀ i ∈ is, i.HasEqn

@[grind] def Pattern.HasEqn (I : Pattern ι n) : Prop :=
  ∀ i ∈ I, i.HasEqn

section Lemmas
variable {i : ι} {is : InstSeq ι} {I : Pattern ι n}

/-! vacuous -/

@[grind =>] theorem Inst.eqnLemma_of_not_mem_results (hx : x ∉ iResults i) :
    i.EqnLemma x ρ := by
  grind [EqnLemma]

@[grind =>] theorem InstSeq.eqnLemma_of_not_mem_results (hx : x ∉ is.results) :
    is.EqnLemma x ρ := by
  intro i hi
  grind

@[grind =>] theorem Pattern.eqnLemma_of_not_mem_results (hx : x ∉ I.results) :
    I.EqnLemma x ρ := by
  intro is his
  grind

/-! structural lemmas -/
variable (I : Pattern ι n) (is : InstSeq ι)

@[simp, grind .] theorem InstSeq.EqnLemma_nil : InstSeq.EqnLemma [] x ρ := by
  grind [InstSeq.EqnLemma]

@[simp, grind =] theorem InstSeq.EqnLemma_cons {i : ι} {is : InstSeq ι} :
    InstSeq.EqnLemma (i :: is) x ρ ↔ i.EqnLemma x ρ ∧ is.EqnLemma x ρ := by
  grind [InstSeq.EqnLemma]

variable {I} in
@[grind .]
theorem Pattern.eqnLemma_of_mem_results_get (hx : x ∈ (I.get k hk).results)
    (wf : I.NoShadowing):
    I.EqnLemma x ρ ↔ (I.get k hk).EqnLemma x ρ := by
  generalize hi : I.get k hk = is
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
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another instruction `j`.
-/
@[grind =>]
theorem InstSeq.eqnLemma_of_eqnLemma_inst (hEqn : is.HasEqn) :
    is.EqnLemma x ρ → ∀ j : Inst, x ∉ j.results → is.EqnLemma x (⟦j⟧ ρ) := by
  grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another instruction `j`.
-/
@[grind =>]
theorem Pattern.eqnLemma_of_eqnLemma_inst (hEqn : I.HasEqn) :
    I.EqnLemma x ρ → ∀ j : Inst, x ∉ j.results → I.EqnLemma x (⟦j⟧ ρ) := by
  grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Pattern.eqnLemma_of_eqnLemma_instSeq (hI : I.HasEqn) :
    I.EqnLemma x ρ → ∀ js : InstSeq, x ∉ js.results → I.EqnLemma x (⟦js⟧ ρ) := by
  intro hI js hjs
  induction js generalizing ρ
  · exact hI
  · grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Inst.eqnLemma_of_eqnLemma_instSeq {i : ι} (hi : i.HasEqn) :
    i.EqnLemma x ρ → ∀ js : InstSeq, x ∉ js.results → i.EqnLemma x (⟦js⟧ ρ) := by
  intro hi js hjs
  induction js generalizing ρ
  · exact hi
  · grind

/-! denote lemmas -/

@[grind =] theorem Inst.regs_denote_of_eqnLemma {i : ι}
    (h : i.EqnLemma x ρ) : (⟦i⟧ ρ).regs x = ρ.regs x := by
  grind [EqnLemma]

@[grind .] theorem InstSeq.regs_denote_of_eqnLemma {is : InstSeq ι} (hEqn : is.HasEqn)
    (hwf : is.NoShadowing) (h : is.EqnLemma x ρ) :
    (⟦is⟧ ρ).regs x = ρ.regs x := by
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
theorem InstSeq.eqnLemma_denote_self (hEqn : is.HasEqn) (hwf : is.NoShadowing)
    (ρ) :
    is.EqnLemma x (⟦is⟧ ρ) := by
  induction is generalizing ρ
  · simp
  · simp; grind

end Lemmas

section EqnLemmaUpTo

/--
`I.usesAt v` is an alias of `I.collapse.usesAt v`.

See `InstSeq.usesAt` for details.
-/
abbrev Pattern.usesAt (v : Var) (I : Pattern ι n) := I.collapse.usesAt v

/--
`I.getDef? v` is an alias of `I.collapse.getDef? v`.

See `InstSeq.getDef?` for details.
-/
abbrev Pattern.getDef? (v : Var) (I : Pattern ι n) : Option Inst :=  I.collapse.getDef? v

/--
`I.EqnLemmaUpTo h ρ` holds when `ρ` satisfies the equation lemma for all
(transitive) dependencies of the `h`-th pattern of `I`.
-/
def Pattern.EqnLemmaUpTo (I : Pattern ι n) (h : Hole n) (ρ : Env ι) : Prop :=
  ∀ x ∈ (I.get h.val).args,
    ∀ y, y = x ∨ y ∈ (I.usesAt x) → I.EqnLemma y ρ

end EqnLemmaUpTo
end EqnLemma

/-!
## Multi Context

We define a notion of a context with multiple holes, also called a multi-context,
by naming each hole.
-/

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

/-! ### Denotation -/
section Denote

instance : Denote (MultiContext n) (HoleEnv n → Env ι → Env ι) where
  denote C η := C.foldl <| fun ρ i =>
                  match i with
                  | .inl (i : ι) => ⟦i⟧ ρ
                  | .inr (h : Hole n) => ⟦η h⟧ ρ

theorem denote_eq : ⟦C⟧ = fun η => C.foldl (fun ρ i =>
                                      match i with
                                      | .inl (i : ι) => ⟦i⟧ ρ
                                      | .inr (h : Hole n) => ⟦η h⟧ ρ) := rfl

@[simp, grind =]
theorem denote_nil : ⟦([] : MultiContext n)⟧ η = id := rfl

@[simp, grind =] theorem denote_cons_inst (i : ι) :
    ⟦.inl i :: C⟧ = fun η ρ => ⟦C⟧ η (⟦i⟧ ρ) := by rfl

@[simp, grind =] theorem denote_cons_hole (h : Hole n) :
    ⟦.inr h :: C⟧ = fun η ρ => ⟦C⟧ η (⟦η h⟧ ρ) := by rfl

end Denote

/-! ### Plugging -/
section Plug

def plug (C : MultiContext n) (I : Pattern ι n) : InstSeq :=
  C.flatMap <| fun i =>
    match i with
    | .inl (i : ι) => [i]
    | .inr (h : Hole n) => I.get h.val

section Lemmas
variable {C}

@[simp, grind =] theorem plug_nil : plug [] I = [] := rfl

@[simp, grind =] theorem plug_cons_inst (i : ι) :
    plug (.inl i :: C) I = i :: plug C I := by rfl

@[simp, grind =] theorem plug_cons_hole (h : Hole n) :
    plug (.inr h :: C) I = I.get h.val ++ plug C I := by rfl

@[simp, grind =]
theorem denote_plug : ⟦C.plug I⟧ = ⟦C⟧ (I.get ·.val) := by
  funext ρ
  induction C generalizing ρ
  case nil => simp
  case cons i C ih => cases i <;> grind

@[grind =] theorem mem_plug_iff (i : ι) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ h, .inr h ∈ C ∧ i ∈ I.get h.val := by
  simp only [plug, List.mem_flatMap]
  constructor
  · grind
  · rintro (_ | ⟨h, _⟩ )
    · grind
    · refine ⟨.inr h, ?_⟩; grind

@[grind =] theorem mem_results_plug_iff {I : Pattern ι n} :
    x ∈ (C.plug I).results ↔
      (∃ i, .inl i ∈ C ∧ x ∈ iResults i) ∨ (∃ h, .inr h ∈ C ∧ x ∈ (I.get h.val).results) := by
  grind

/-! #### Completeness -/

@[grind =] theorem mem_plug_iff_of_complete (hC : C.Complete) (i : ι) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ (h : Hole n), i ∈ I.get h.val := by
  grind

/--
If context `C` is complete, then the results of pattern `I` are a subset of the
results of `C.plug I`.
-/
theorem results_subset_results_plug (hC : C.Complete) :
    I.results ⊆ (C.plug I).results := by
  grind [Pattern.mem_iff_get_hole]
grind_pattern results_subset_results_plug => (C.plug I).results

/-! ### WellFormedness -/

def embedPlugAux (p : I.PC) (C : MultiContext n) (hC : .inr p.hole ∈ C) : (C.plug I).PC :=
  match C with
  | .inl i :: C => (embedPlugAux p C (by grind)).succ
  | .inr h :: C =>
      if _ : h = p.hole then
        (p.pc.cast <| by grind).appendLeft
      else
        (embedPlugAux p C (by grind)).appendRight

open InstSeq (PC) in
def embedPlug (I : Pattern ι n) (C : MultiContext n) (hC : C.Complete) :
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

def noShadowing_pattern_of_plug_noShadowing {n} {C : MultiContext n} {I : Pattern ι n}
    (hC : C.Complete) :
    (C.plug I).NoShadowing → I.NoShadowing := by
  simp only [InstSeq.noShadowing_iff, ne_eq]
  intro ns i j hij
  let f := C.embedPlug I hC
  have := ns (f i) (f j)
  grind

end Lemmas
end Plug
end MultiContext

/-!
## Denotational Refinement & Equivalence
-/
section Denotational

/--
A pattern `I` is denotationally refined by pattern `J`,
when for any hole `h` and environments such that `ρ ⊆ η` and
`ρ` (resp `η`) satisfies the equation lemma for all (transitive) dependencies
of the `h`-th sequence of `I` (resp `J`), it is the case that the denotation of
`h`-th of `I` under `ρ` is refined by the denotation of the `h`-th hole of `J`
under `η`.

TODO: We ought to prove that this condition is actually implied by the much more
simple `⟦I⟧ ρ ⊆ ⟦J⟧ ρ` with some side-condition on the variables of each pattern
in `I` and `J`.
-/
def Pattern.DenRefine (I J : Pattern ι n) : Prop :=
  ∀ h : Hole n, ∀ ρ η,
    I.EqnLemmaUpTo h ρ →
    J.EqnLemmaUpTo h η →
    ⟦I.get h.val⟧ ρ ⊆ ⟦J.get h.val⟧ η

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
    ⟦I.get h.val⟧ ρ = ⟦J.get h.val⟧ η

end Denotational

/-!
## Contextual Refinement & Equivalence
-/
section Contextual

/--
A pattern `I` is contextually refined by pattern `J`,
when for any complete context `C` such that `C[I]` and `C[J]` are both
wellformed, `C[I]` is (denotationally) refined by `C[J]`.
-/
def Pattern.CtxRefine (I J : Pattern ι n) : Prop :=
  ∀ (C : MultiContext n), C.Complete →
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed ∅ → CJ.WellFormed ∅ →
      ⟦CI⟧ {} ⊆ ⟦CJ⟧ {}

/--
Two patterns `I` and `J` are contextually equivalent,
when for any complete context `C` such that `C[I]` and `C[J]` are both
wellformed, `C[I]` is (denotationally) equivalent to `C[J]`.
-/
def Pattern.CtxEquiv (I J : Pattern ι n) : Prop :=
  ∀ (C : MultiContext n), C.Complete →
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed ∅ → CJ.WellFormed ∅ →
      ⟦CI⟧ {} = ⟦CJ⟧ {}

end Contextual



/-!
## Residual
-/
section Residual

/--
We say that `Γ` is a residual of context `C` under pattern `I` when

TODO: dedup with Invariant
-/
@[grind, grind cases]
private structure Residual (Γ : VarSet _) (C : MultiContext n) (I : Pattern ι n) where
  /-- `C.plug I` is well-formed with free variables `Γ`. -/
  wf : (C.plug I).WellFormed Γ
  residual : ∀ x ∈ I.results, x ∉ Γ → (∃ h, .inr h ∈ C ∧ x ∈ (I.get h.val).results)

namespace Residual

/-! invariants -/

private theorem initial (wf : (C.plug I).WellFormed ∅) (hC : C.Complete) : Residual ∅ C I := by
  grind [Pattern.mem_iff_get_hole]

@[grind →] private theorem of_cons_inst :
    Residual Γ (.inl i :: C) I → Residual (iResults i ∪ Γ) C I := by
  rintro ⟨wf, residual⟩; constructor
  · grind
  · intro x; have := residual x; grind

@[grind →] private theorem of_cons_hole  :
    Residual Γ (.inr h :: C) I → Residual ((I.get h.val).results ∪ Γ) C I := by
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
    (Γ : VarSet _) (C : MultiContext n) (I : Pattern ι n) (ρ : Env ι)
    extends Residual Γ C I where
  /--
  If `x ∈ Γ`, then any transitive dependencies of `x` (in `I`) are also
  part of `Γ`.
  -/
  closed : ∀ x ∈ Γ, ∀ y ∈ I.usesAt x, y ∈ Γ
  eqn : ∀ x ∈ Γ, I.EqnLemma x ρ
  ns : I.NoShadowing


namespace Invariant
variable {Γ} {C : MultiContext n} {I : Pattern ι n} {ρ : Env ι} {i : ι}

private theorem initial (wf : (C.plug I).WellFormed ∅) (hC : C.Complete) : Invariant ∅ C I { } := by
  have nsI : I.NoShadowing := by
    apply C.noShadowing_pattern_of_plug_noShadowing
    <;> grind
  grind [Pattern.mem_iff_get_hole]

private theorem of_invariant_cons_inst (hI : I.HasEqn := by assumption) :
    Invariant Γ (.inl i :: C) I ρ → Invariant (iResults i ∪ Γ) C I (⟦i⟧ ρ) := by
  rintro ⟨residual, closed, eqn, nsI⟩
  have : ∀ x ∈ iResults i, x ∉ I.results := by
    intro x hx hxI
    have : x ∉ (C.plug I).results := by grind
    obtain ⟨h, hhC, hhx⟩ : ∃ h, Sum.inr h ∈ C ∧ x ∈ (I.get h.val).results := by
      have : x ∉ Γ := by grind
      have := residual.residual x hxI;
      grind
    grind
  constructor
  <;> grind

private theorem of_invariant_cons_hole (hI : I.HasEqn := by assumption) :
    Invariant Γ (.inr h :: C) I ρ →
    Invariant ((I.get h.val).results ∪ Γ) C I (⟦I.get h.val⟧ ρ) := by
  rintro ⟨residual, closed, eqn, nsI⟩
  generalize his : I.get h.val = is at *
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
        change InstSeq at is
        have his : is ⊆ I.collapse := by grind
        have hΔ' : is.args ⊆ iResults i ∪ Δ := by grind
        specialize ih his _ hΔ'
        specialize ih <| by -- prove closedness
          clear ih
          intro x hx y hy
          by_cases x ∈ Δ; grind
          have : x ∈ iResults i := by grind
          · rw [InstSeq.mem_usesAt'] at hy
            obtain ⟨j, hj, hxj, hy⟩ := hy
            obtain rfl : i = j := by
              have hi : i ∈ I.collapse := by grind
              have hj : j ∈ I.collapse := by grind
              apply InstSeq.eq_of_not_disjoint_results_of_noShadowing hi hj nsI
              grind
            rcases hy with ( (hy : y ∈ i.args) | ⟨z, hzi, hyz⟩ )
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

  suffices ∀ ρ η, ρ ⊆ η →
      ∀ {Γ}, Invariant Γ C I ρ →
      ∀ {Δ}, Invariant Δ C J η →
      ⟦C⟧ (I.get ·.val) ρ ⊆ ⟦C⟧ (J.get ·.val) η by
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
        let is := I.get h.val
        let js := J.get h.val
        apply ih (⟦is⟧ ρ) (⟦js⟧ η)
        · have : is ∈ I := by grind [Pattern.mem_iff_get]
          have : js ∈ J := by grind [Pattern.mem_iff_get]
          apply h_denoteRefine
          · intro x (hx : x ∈ is.args) y hy
            have : is.args ⊆ Γ := by grind
            rcases hCI
            grind
          · intro x (hx : x ∈ js.args)
            have : js.args ⊆ Δ := by grind
            rcases hCJ
            grind
        · apply Invariant.of_invariant_cons_hole hI hCI
        · apply Invariant.of_invariant_cons_hole hJ hCJ

/--
Proving denotational equivalence is sufficient for showing contextual equivalence.
-/
theorem Pattern.ctxEquiv_of_denoteEquiv (I J : Pattern ι n)
    (hI : I.HasEqn) (hJ : J.HasEqn) (h_denoteEquiv : I.DenEquiv J) :
    I.CtxEquiv J := by
  intro C hC CI CJ hCI hCJ
  have : I.DenRefine J ∧ J.DenRefine I := by grind [DenRefine, DenEquiv]
  apply Env.refine_antisymm
  <;> apply ctxRefine_of_denoteRefine
  <;> grind
