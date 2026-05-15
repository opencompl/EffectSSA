module

public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.VarSet

/-!
# Instruction Sequence
-/
namespace EffectSSA.ProofSketch
open VarSet

@[expose] public abbrev InstSeq := List Inst

namespace InstSeq

/-!
## Variables
-/
noncomputable section Vars

@[grind]
def argsResults : InstSeq → VarSet × VarSet := go ∅ ∅
where go (A R : VarSet)
  | [] => (A, R)
  | i :: is =>
    let A := A ∪ (i.args - R)
    let R := R ∪ i.results
    go A R is

/--
`is.args` is the set of free arguments used in sequence `is`.

Note: "free" means that any argument of an instruction `i ∈ is` that is also the
result of any preceding instructions are *not* included in `is.args`.
-/
public def args (is : InstSeq) : VarSet :=
  is.argsResults.1

/-- `is.results` is the set of all results of sequence `is`. -/
public def results (is : InstSeq) : VarSet :=
  is.argsResults.2

section Lemmas
variable {i : Inst} {is : InstSeq}
attribute [local grind] results args argsResults argsResults.go

@[grind =] theorem argsResults_go_fst (A R : VarSet) :
    (argsResults.go A R is).1 = A ∪ (args is - R) := by
  suffices ∀ A' R',
    (argsResults.go (A ∪ (A' - R)) (R ∪ R') is).fst = A ∪ ((argsResults.go A' R' is).fst - R)
  by simp [args, argsResults]; grind
  induction is generalizing A R <;> grind

@[simp, grind =] public theorem args_nil : args [] = ∅ := by rfl
@[simp, grind =] public theorem args_cons :
    args (i :: is) = i.args ∪ (args is - i.results) := by
  show (argsResults.go ..).fst = _; grind

@[grind =] theorem argsResults_go_snd : (argsResults.go A R is).2 = R ∪ is.results := by
  suffices ∀ A' R',
    (argsResults.go A (R ∪ R') is).snd = R ∪ (argsResults.go A' R' is).snd
  by simp [results, argsResults]; grind
  induction is generalizing A R <;> grind

@[simp, grind =] public theorem results_nil  : results [] = ∅ := by rfl
@[simp, grind =] public theorem results_cons : results (i :: is) = i.results ∪ is.results := by
  show (argsResults.go ..).snd = _; grind

@[simp, grind =] public theorem results_append {xs ys : InstSeq} :
    results (xs ++ ys) = xs.results ∪ ys.results := by
  induction xs <;> grind

@[grind =] public theorem mem_results_iff : x ∈ is.results ↔ ∃ i ∈ is, x ∈ i.results := by
  induction is <;> grind

@[grind →] public theorem mem_results_of_mem_inst {x : Var} (hi : i ∈ is) (hx : x ∈ i.results) :
    x ∈ is.results := by
  grind

@[grind →] public theorem results_subset_of_mem (h : i ∈ is) : i.results ⊆ is.results := by
  grind

/--
Recall that `is.args` contains only the *free* arguments of `is`, hence, for some `i ∈ is`,
in general `i.args ⊈ is.args`. Instead, an argument `x ∈ i.args` might either be
free (thus in `is.args`), or might refer to the result of an earlier instruction;
the latter we over-approximate by the results of all instructions (`is.results`)
-/
@[grind →] public theorem args_subset_of_mem (h : i ∈ is) :
    i.args ⊆ is.args ∪ is.results := by
  induction is <;> grind

end Lemmas

/-! ### getDef / usesAt  -/

/--
`is.getDef? v` returns an instruction `i ∈ is` s.t. `v ∈ i.results`,
or `none` if no such instruction exists
-/
public noncomputable def getDef? (v : Var) : (is : InstSeq) → Option { i // i ∈ is ∧ v ∈ is.results }
  | [] => none
  | i :: is =>
      open Classical in
      if hi : v ∈ i.results then
        some ⟨i, by grind⟩
      else
        (getDef? v is).map (fun ⟨i, hi⟩ => ⟨i, by grind⟩)

/-- `is.UsesAt y x` is true when `y` is a (transitive) dependency of `x`. -/
@[grind cases]
public inductive UsesAt (is : InstSeq) (y : Var) : Var → Prop
  | arg  : i ∈ is → x ∈ i.results → y ∈ i.args → UsesAt is y x
  | trans : i ∈ is → x ∈ i.results → z ∈ i.args → UsesAt is y z → UsesAt is y x

/--
`is.usesAt v` is the set of all transitive arguments that are used to compute
variable `v`.

That is, if `v` is defined by instruction `i ∈ is`, then `is.usesAt v` is the
union of `i.args` with the recursive set `{ is.usesAt y | y ∈ i.args }`.

If no instruction of `is` defines the variable `v` as a result,
then `is.usesAt v` is the empty set.
-/
public def usesAt (x : Var) (is : InstSeq) : VarSet :=
  { y | is.UsesAt y x }

section Lemmas
variable {is : InstSeq}

@[simp, grind =] public theorem mem_usesAt : y ∈ is.usesAt x ↔ is.UsesAt y x := by
  simp [usesAt]

public theorem mem_usesAt' :
    y ∈ is.usesAt x ↔ ∃ i ∈ is, x ∈ i.results ∧ (y ∈ i.args ∨ ∃ z ∈ i.args, y ∈ is.usesAt z) := by
  constructor
  · grind
  · simp only [mem_usesAt, forall_exists_index, and_imp]
    rintro i hi hxi ( hy | ⟨z, hzi, hyz⟩)
    · apply UsesAt.arg hi hxi hy
    · apply UsesAt.trans hi hxi hzi hyz

@[simp, grind .] public theorem not_usesAt_nil : ¬(UsesAt [] y x) := by grind
@[simp, grind =] public theorem usesAt_nil_eq : usesAt x [] = ∅ := by grind

@[simp, grind =>]
public theorem usesAt_eq_of_not_mem_results {x : Var} (h : x ∉ is.results) :
    is.usesAt x = ∅ := by
  induction is <;> grind [usesAt]

end Lemmas
end Vars


/-!
## WellFormed
In a well-formed SSA program, shadowing of variables is not allowed.
-/
public section WellFormed

/--
`is.NoShadowing` holds if no two instructions in `is` define the same
resulting variable.
-/
inductive NoShadowing : InstSeq → Prop
  | nil : NoShadowing []
  | cons {i : Inst} {is : InstSeq} :
      i.results.Disjoint is.results → NoShadowing is
      → NoShadowing (i :: is)

/--
A sequence `is` is well-formed, w.r.t. free variables `Γ`, when

* `is` has no shadowing of results,
* the arguments of `is` are contained in `Γ`, and
* `Γ` does not contain any result of `is`.
-/
@[grind, grind cases]
structure WellFormed (Γ : VarSet) (is : InstSeq)  where
  noShadowing : is.NoShadowing
  args : is.args ⊆ Γ
  results : is.results.Disjoint Γ

section Lemmas
variable {is js : InstSeq}

/-! ### Grind Annotations -/
section Grind

grind_pattern WellFormed.noShadowing => is.WellFormed Γ
grind_pattern WellFormed.results => is.WellFormed Γ, is.results
grind_pattern WellFormed.args => is.WellFormed Γ, is.args

end Grind

/-! ### Basic Unfolding Lemmas -/
section Basic
attribute [local grind] WellFormed NoShadowing

@[grind ., simp] theorem noShadowing_nil : NoShadowing [] := by grind
@[grind =, simp] theorem noShadowing_cons :
    NoShadowing (i :: is) ↔ i.results.Disjoint is.results ∧ NoShadowing is := by grind

@[grind =, simp] theorem noShadowing_append :
    NoShadowing (is ++ js) ↔ is.results.Disjoint js.results ∧ is.NoShadowing ∧ js.NoShadowing := by
  induction is <;> grind

@[grind ., simp] theorem wellFormed_nil : WellFormed Γ [] := by grind
@[grind =, simp] theorem wellFormed_cons :
    WellFormed Γ (i :: is) ↔
      i.args ⊆ Γ ∧ Γ.Disjoint i.results ∧ is.WellFormed (i.results ∪ Γ) := by
  constructor
  · rintro ⟨⟩
    and_intros
    · grind
    · grind
    · constructor <;> grind
  · rintro ⟨⟩; constructor <;> grind

@[grind =, simp] theorem wellFormed_append :
    WellFormed Γ (is ++ js) ↔
      is.WellFormed Γ ∧ js.WellFormed (is.results ∪ Γ) := by
  induction is generalizing Γ <;> grind

end Basic

/-! ### Results -/
section ResultLemmas

theorem eq_of_not_disjoint_results_of_noShadowing {i j : Inst}
    (hi : i ∈ is) (hj : j ∈ is) (wf : is.NoShadowing) :
    ¬(i.results.Disjoint j.results) → i = j := by
  induction is <;> grind
grind_pattern eq_of_not_disjoint_results_of_noShadowing =>
  i.results.Disjoint j.results, i ∈ is, j ∈ is, is.NoShadowing
  -- ^^ TODO: this pattern seems overly specific, maybe I could drop the Disjoint pattern

end ResultLemmas

/-! ### Sublist -/

end Lemmas
end WellFormed



end InstSeq
