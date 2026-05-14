module

public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.VarSet

/-!
# Instruction Sequence
-/
namespace EffectSSA.ProofSketch

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

/--
`is.usesAt v` is the set of all transitive arguments that are used to compute
variable `v`.

That is, if `v` is defined by instruction `i ∈ is`, then `is.usesAt v` is the
union of `i.args` with the recursive set `{ is.usesAt y | y ∈ i.args }`.

If no instruction of `is` defines the variable `v` as a result,
then `is.usesAt v` is the empty set.
-/
public noncomputable def usesAt (v : Var) : InstSeq → VarSet
  | [] => ∅
  | i :: (is : InstSeq) =>
      open Classical in
      if v ∈ i.results then
        i.args ∪ i.args.flatMap (is.usesAt ·)
      else
        is.usesAt v

section Lemmas
variable {is : InstSeq}

@[simp, grind =>]
public theorem usesAt_eq_of_not_mem_results {x : Var} (h : x ∉ is.results) :
    is.usesAt x = ∅ := by
  induction is <;> grind [usesAt]

@[grind =]
public theorem mem_usesAt :
    y ∈ is.usesAt x ↔ ∃ i ∈ is, x ∈ i.results ∧
      (y ∈ i.args ∨ ∃ z ∈ i.args, y ∈ is.usesAt z) := by
  induction is generalizing y
  · grind [usesAt]
  case cons i is ih =>
    stop
    by_cases y ∈ i.results
    · have : usesAt x (i :: is) = i.args ∪ i.args.flatMap (usesAt · is) := by
        sorry
      simp_all
      grind
    split
    · grind
    · simp_all

end Lemmas
end Vars
end InstSeq
