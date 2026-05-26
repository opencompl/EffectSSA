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

public import Std.Data.HashMap

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

/-! ### Definition -/

/-- `State` is the type of global runtime state (e.g, memory) -/
axiom State : Type

axiom State.initial : State

/--
A stateful environment `e : SEnv`
bundles a pure environment with a global state.
-/
structure SEnv where
  /-- A partial map from variables (i.e, virtual registers) to values. -/
  regs : Var → Option Val := fun _ => none
  /-- The global state, e.g, for memory and UB -/
  state : State := .initial

/-! ### Defs -/

axiom Inst.denote : Inst → SEnv → SEnv
instance : Denote Inst (SEnv → SEnv) where
  denote := Inst.denote

/--
An `InstSeq` is evaluated by evaluating each instruction in turn,
threading the environment through.
-/
@[default_instance]
instance : Denote InstSeq (SEnv → SEnv) where
  denote is := is.foldl (fun e i => ⟦i⟧ e)

/--
A `Pattern` is evaluated by collapsing it into an instruction sequence,
and evaluating that.
-/
instance : Denote (Pattern n) (SEnv → SEnv) where
  denote I := ⟦I.collapse⟧

/-! ### Properties -/
section Properties

theorem InstSeq.denote_eq {is : InstSeq} :
    ⟦is⟧ = is.foldl (fun e (i : Inst) => ⟦i⟧ e) := by rfl

@[simp, grind =] theorem InstSeq.denote_nil : ⟦[]⟧ = id := by rfl
@[simp, grind =] theorem InstSeq.denote_nil_apply : ⟦[]⟧ ρ = ρ := by rfl

@[simp, grind =] theorem InstSeq.denote_cons : ⟦i ;> is⟧ = fun ρ => ⟦is⟧ (⟦i⟧ ρ) := by rfl

@[simp, grind =] theorem InstSeq.denote_append (is js : InstSeq) :
    ⟦is ++ js⟧ = fun ρ => ⟦js⟧ (⟦is⟧ ρ) := by
  grind [InstSeq.denote_eq]


@[grind =] theorem Pattern.denote_eq {I : Pattern n} :
    ⟦I⟧ = ⟦I.collapse⟧ := by rfl

@[simp, grind =] theorem Pattern.denote_nil {I : Pattern 0} : ⟦I⟧ = id := by
  cases I; rfl

@[simp, grind =]
theorem Pattern.denote_cons  (is : InstSeq) (I : Pattern n) :
    ⟦cons is I⟧ = fun ρ => ⟦I⟧ (⟦is⟧ ρ) := by
  simp [Pattern.denote_eq]

/-! results -/
variable {x : Var}

/-- Instructions only modify the registers in their `results` set. -/
@[grind .] axiom Inst.regs_denote_of_not_mem_results (i : Inst) {x : Var} {ρ : SEnv}
    (h : x ∉ i.results) : (⟦i⟧ ρ).regs x = ρ.regs x

@[grind =] theorem InstSeq.regs_denote_of_not_mem_results (h : x ∉ is.results) :
    (⟦is⟧ ρ).regs x = ρ.regs x := by
  induction is generalizing ρ <;> grind

end Properties

/-! #### MultiContext Semantics -/
namespace MultiContext
variable (C : MultiContext n)

instance : Denote (MultiContext n) (HoleEnv n → SEnv → SEnv) where
  denote C η := C.foldl <| fun ρ i =>
                  match i with
                  | .inl (i : Inst) => ⟦i⟧ ρ
                  | .inr (h : Hole n) => ⟦η h⟧ ρ

theorem denote_eq : ⟦C⟧ = fun η => C.foldl (fun ρ i =>
                                      match i with
                                      | .inl (i : Inst) => ⟦i⟧ ρ
                                      | .inr (h : Hole n) => ⟦η h⟧ ρ) := rfl

@[simp, grind =]
theorem denote_nil : ⟦([] : MultiContext n)⟧ η = id := rfl

@[simp, grind =] theorem denote_cons_inst (i : Inst) :
    ⟦.inl i :: C⟧ = fun η ρ => ⟦C⟧ η (⟦i⟧ ρ) := by rfl

@[simp, grind =] theorem denote_cons_hole (h : Hole n) :
    ⟦.inr h :: C⟧ = fun η ρ => ⟦C⟧ η (⟦η h⟧ ρ) := by rfl

@[simp, grind =]
theorem denote_plug : ⟦C.plug I⟧ = ⟦C⟧ (I[·]) := by
  funext ρ
  induction C generalizing ρ
  case nil => simp
  case cons i C ih => cases i <;> grind

end MultiContext
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
def SEnv.EquivOn (P : Var → Prop) : SEnv → SEnv → Prop := fun ρ η =>
  ρ.state = η.state
  ∧ (∀ v, P v → ρ.regs v = η.regs v)

/-- If two environments are equivalent on all variables, they are equal. -/
theorem SEnv.eq_of_equivOn {ρ η} : EquivOn (fun _ => True) ρ η → ρ = η := by
  rcases ρ with ⟨ρ_regs, ρ_state⟩
  rcases η with ⟨η_regs, η_state⟩
  simp only [EquivOn]
  intro h
  have : ρ_regs = η_regs := by funext; simp_all
  simp_all

section Lemmas
attribute [local grind] SEnv.EquivOn

/-
TODO: axiomatise the relevant properties of equivalence on states and values,
      then use those axioms to prove the SEnv.equiv_foo assumptions below.
-/

@[simp, grind ., refl]
theorem SEnv.equivOn_refl (ρ : SEnv) : EquivOn P ρ ρ := by
  grind

theorem SEnv.equiv_trans {ρ₁ ρ₂ ρ₃ : SEnv} : EquivOn P ρ₁ ρ₂ → EquivOn P ρ₂ ρ₃ → EquivOn P ρ₁ ρ₃ := by
  grind

theorem SEnv.equiv_symm {ρ₁ ρ₂ : SEnv} : EquivOn P ρ₁ ρ₂ → EquivOn P ρ₂ ρ₁ := by grind
grind_pattern SEnv.equiv_symm => SEnv.EquivOn P ρ₁ ρ₂

end Lemmas
end Equiv

/-!
## Refinement
-/
section Refine

@[instance] axiom State.Refine : Refinement State
@[instance] axiom Val.Refine : Refinement Val

/--
We say that `ρ` is a sub-environment of `η`, written as `ρ ⊒ η`,

* the global state of `ρ` is refined by the global state of `η`, and
* for each variable `v` in the domain of `ρ`,
    the value `ρ v` is refined by `η v`.
-/
instance : Refinement SEnv where
  IsRefinedBy ρ η := ρ.state ⊒ η.state ∧ (∀ v, ρ.regs v ⊒ η.regs v)
  antisymm := by
    rintro ⟨s, ρ⟩ ⟨t, η⟩ hxy hyx
    suffices s = t ∧ ρ = η by grind
    grind

section RefineLemmas

/-! #### Congruence Lemmas -/
section RefineCongr

/--
We assume that each instruction's semantics preserves refinement.

In other words, the semantics are *monotone* w.r.t. the refinement relation.
-/
@[grind .] axiom Inst.denote_isRefinedBy_congr (hρ : ρ₁ ⊒ ρ₂) (i : Inst) :
    ⟦i⟧ ρ₁ ⊒ ⟦i⟧ ρ₂

@[grind .] theorem InstSeq.denote_isRefinedBy_congr (hρ : ρ₁ ⊒ ρ₂) (is : InstSeq) :
    ⟦is⟧ ρ₁ ⊒ ⟦is⟧ ρ₂ := by
  induction is generalizing ρ₁ ρ₂
  · simpa
  · grind

@[grind .] theorem Pattern.denote_isRefinedBy_congr (hρ : ρ₁ ⊒ ρ₂) (I : Pattern n) :
    ⟦I⟧ ρ₁ ⊒ ⟦I⟧ ρ₂ := by
  simp [Pattern.denote_eq, InstSeq.denote_isRefinedBy_congr hρ]

end RefineCongr
end RefineLemmas
end Refine

/-!
## Equation Lemma
-/
section EqnLemma

def Inst.EqnLemma (i : Inst) (x : Var) (ρ : SEnv) : Prop :=
  x ∈ i.results → (⟦i⟧ ρ).regs x = ρ.regs x

@[grind] def InstSeq.EqnLemma (is : InstSeq) (x : Var) (ρ : SEnv) : Prop :=
  ∀ i ∈ is, i.EqnLemma x ρ

@[grind] def Pattern.EqnLemma (I : Pattern n) (x : Var) (ρ : SEnv) : Prop :=
  ∀ i ∈ I, i.EqnLemma x ρ

/--
We say that an instruction `i` has a well-behaved equation lemma when:

* validity of the equation lemma is stable under the execution of more instructions, and
* executing `i` is guaranteed to yield an environment that satisfies its
  own equation lemma
-/
structure Inst.HasEqn (i : Inst) : Prop where
  stable : ∀ x ρ, i.EqnLemma x ρ → ∀ j : Inst, x ∉ j.results → i.EqnLemma x (⟦j⟧ ρ)
  idempotent : ∀ x ρ, i.EqnLemma x (⟦i⟧ ρ)

@[grind] def InstSeq.HasEqn (is : InstSeq) : Prop :=
  ∀ i ∈ is, i.HasEqn

@[grind] def Pattern.HasEqn (I : Pattern n) : Prop :=
  ∀ i ∈ I, i.HasEqn

section Lemmas
variable {i : Inst} {is : InstSeq} {I : Pattern n}

/-! vacuous -/

@[grind =>] theorem Inst.eqnLemma_of_not_mem_results (hx : x ∉ i.results) :
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
variable (I : Pattern n) (is : InstSeq)

@[simp, grind .] theorem InstSeq.EqnLemma_nil : InstSeq.EqnLemma [] x ρ := by
  grind [InstSeq.EqnLemma]

@[simp, grind =] theorem InstSeq.EqnLemma_cons {i : Inst} {is : InstSeq} :
    InstSeq.EqnLemma (i ;> is) x ρ ↔ i.EqnLemma x ρ ∧ is.EqnLemma x ρ := by
  grind [InstSeq.EqnLemma]

variable {I} in
@[grind .]
theorem Pattern.eqnLemma_of_mem_results_get {k : Nat} {hk}
    (hx : x ∈ I[k].results) (wf : I.NoShadowing):
    I.EqnLemma x ρ ↔ I[k].EqnLemma x ρ := by
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
theorem Inst.eqnLemma_of_eqnLemma_instSeq {i : Inst} (hi : i.HasEqn) :
    i.EqnLemma x ρ → ∀ js : InstSeq, x ∉ js.results → i.EqnLemma x (⟦js⟧ ρ) := by
  intro hi js hjs
  induction js generalizing ρ
  · exact hi
  · grind

/-! denote lemmas -/

@[grind =] theorem Inst.regs_denote_of_eqnLemma {i : Inst}
    (h : i.EqnLemma x ρ) : (⟦i⟧ ρ).regs x = ρ.regs x := by
  grind [EqnLemma]

@[grind .] theorem InstSeq.regs_denote_of_eqnLemma {is : InstSeq} (hEqn : is.HasEqn)
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
abbrev Pattern.usesAt (v : Var) (I : Pattern n) := I.collapse.usesAt v

/--
`I.getDef? v` is an alias of `I.collapse.getDef? v`.

See `InstSeq.getDef?` for details.
-/
abbrev Pattern.getDef? (v : Var) (I : Pattern n) : Option Inst :=  I.collapse.getDef? v

/--
`I.EqnLemmaUpTo h ρ` holds when `ρ` satisfies the equation lemma for all
(transitive) dependencies of the `h`-th pattern of `I`.
-/
def Pattern.EqnLemmaUpTo (I : Pattern n) (h : Hole n) (ρ : SEnv) : Prop :=
  ∀ x ∈ I[h].args,
    ∀ y, y = x ∨ y ∈ (I.usesAt x) → I.EqnLemma y ρ

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
def Pattern.DenRefine (I J : Pattern n) : Prop :=
  ∀ h : Hole n, ∀ ρ η,
    I.EqnLemmaUpTo h ρ →
    J.EqnLemmaUpTo h η →
    ⟦ I[h] ⟧ ρ ⊒ ⟦ J[h] ⟧ η

/--
A pattern `I` is denotationally equivalent to pattern `J`,
when for any hole `h` and environments `ρ` which satisfies the equation lemma
for all (transitive) dependencies of the `h`-th hole of both `I` and `J`,
it is the case that the denotation of `h`-th of `I` is equal to the denotation
of the `h`-th hole of `J`.
-/
def Pattern.DenEquiv (I J : Pattern n) : Prop :=
  ∀ h : Hole n, ∀ ρ η,
    I.EqnLemmaUpTo h ρ →
    J.EqnLemmaUpTo h η →
    ⟦ I[h] ⟧ ρ = ⟦ J[h] ⟧ η

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
def Pattern.CtxRefine (I J : Pattern n) : Prop :=
  ∀ (C : MultiContext n), C.Complete →
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed ∅ → CJ.WellFormed ∅ →
      ⟦CI⟧ {} ⊒ ⟦CJ⟧ {}

/--
Two patterns `I` and `J` are contextually equivalent,
when for any complete context `C` such that `C[I]` and `C[J]` are both
wellformed, `C[I]` is (denotationally) equivalent to `C[J]`.
-/
def Pattern.CtxEquiv (I J : Pattern n) : Prop :=
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
private structure Residual (Γ : VarSet) (C : MultiContext n) (I : Pattern n) where
  /-- `C.plug I` is well-formed with free variables `Γ`. -/
  wf : (C.plug I).WellFormed Γ
  residual : ∀ x ∈ I.results, x ∉ Γ → (∃ h, .inr h ∈ C ∧ x ∈ I[h].results)

namespace Residual

/-! invariants -/

private theorem initial (wf : (C.plug I).WellFormed ∅) (hC : C.Complete) : Residual ∅ C I := by
  grind [Pattern.mem_iff_getElem_hole]

@[grind →] private theorem of_cons_inst :
    Residual Γ (.inl i :: C) I → Residual (i.results ∪ Γ) C I := by
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
    (Γ : VarSet) (C : MultiContext n) (I : Pattern n) (ρ : SEnv)
    extends Residual Γ C I where
  /--
  If `x ∈ Γ`, then any transitive dependencies of `x` (in `I`) are also
  part of `Γ`.
  -/
  closed : ∀ x ∈ Γ, ∀ y ∈ I.usesAt x, y ∈ Γ
  eqn : ∀ x ∈ Γ, I.EqnLemma x ρ
  ns : I.NoShadowing


namespace Invariant
variable {Γ} {C : MultiContext n} {I : Pattern n} {ρ : SEnv} {i : Inst}

private theorem initial (wf : (C.plug I).WellFormed ∅) (hC : C.Complete) : Invariant ∅ C I { } := by
  have nsI : I.NoShadowing := by
    apply C.noShadowing_pattern_of_plug_noShadowing
    <;> grind
  grind [Pattern.mem_iff_getElem_hole]

private theorem of_invariant_cons_inst (hI : I.HasEqn := by assumption) :
    Invariant Γ (.inl i :: C) I ρ → Invariant (i.results ∪ Γ) C I (⟦i⟧ ρ) := by
  rintro ⟨residual, closed, eqn, nsI⟩
  have : ∀ x ∈ i.results, x ∉ I.results := by
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
        have hΔ' : is.args ⊆ i.results ∪ Δ := by grind
        specialize ih his _ hΔ'
        specialize ih <| by -- prove closedness
          clear ih
          intro x hx y hy
          by_cases x ∈ Δ; grind
          have : x ∈ i.results := by grind
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
theorem Pattern.ctxRefine_of_denoteRefine (I J : Pattern n)
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

/--
Proving denotational equivalence is sufficient for showing contextual equivalence.
-/
theorem Pattern.ctxEquiv_of_denoteEquiv (I J : Pattern n)
    (hI : I.HasEqn) (hJ : J.HasEqn) (h_denoteEquiv : I.DenEquiv J) :
    I.CtxEquiv J := by
  intro C hC CI CJ hCI hCJ
  have : I.DenRefine J ∧ J.DenRefine I := by grind [DenRefine, DenEquiv]
  apply Refinement.antisymm
  <;> apply ctxRefine_of_denoteRefine
  <;> grind


/-!
# Control Flow
-/

/-!
## AST
-/
section AST

axiom Terminator : Type

structure Block n where
  insts : MultiContext n
  term : Terminator

structure BlockId where
  id : String
deriving Hashable, DecidableEq

/--
`CFG n` is a control-flow graph with `n` holes.

TODO: incorporate `Context` in the name somehow.
-/
structure CFG n where
  blocks : Std.HashMap BlockId (Block n)
  entry : BlockId

abbrev Program := CFG 0

end AST

/-!
## Semantics
-/
section Semantics

#check Denote

axiom Terminator.denote : Denote Terminator _

end Semantics
