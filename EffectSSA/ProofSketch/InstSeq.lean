module

public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Effect

/-!
# Instruction Sequence
-/
namespace EffectSSA.ProofSketch
open VarSet
open ITree

public abbrev InstSeq := List Inst


/-!
## Custom Cons Notation
We set up `;>` as a wrapper around `::` which includes an `InstSeq` type
annotation, to avoid leaking the definition as a `List`.
We then also include custom induction & cases principle for the same purpose.
-/
section Cons

@[grind, match_pattern] public abbrev InstSeq.cons : Inst → InstSeq → InstSeq :=
  (· :: ·)

scoped infixl:67 " ;> " => InstSeq.cons

namespace InstSeq

@[induction_eliminator, elab_as_elim]
public noncomputable def rec {motive : InstSeq → Sort u} :
    (nil : motive []) →
    (cons : (head : Inst) → (tail : InstSeq) → motive tail → motive (head ;> tail)) →
    ∀ is, motive is := List.rec

@[cases_eliminator, elab_as_elim]
public noncomputable def cases {motive : InstSeq → Sort u}
    (nil : motive [])
    (cons : (head : Inst) → (tail : InstSeq) → motive (head ;> tail)) :
    ∀ is, motive is :=
  (List.casesOn · nil cons)

end InstSeq
end Cons

namespace InstSeq

variable {ι : Type} {ε : ι → Type}

/-!
## Denotation
-/

/--
Denote an `InstSeq` into an ITree with `InstEff`s, i.e,
where each instruction has a unique effect associated with it.
-/
public def denote : (is : InstSeq) → ITree InstEff Unit
  | i :: is => Effect.trigger InstEff i *> denote is
  | [] => .ret ()

/-!
## Variables
-/
noncomputable section Vars

@[grind]
def argsResults : InstSeq → VarSet × VarSet := go ∅ ∅
where go (A R : VarSet)
  | [] => (A, R)
  | i ;> is =>
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
    args (i ;> is) = i.args ∪ (args is - i.results) := by
  show (argsResults.go ..).fst = _; grind

@[grind =] theorem argsResults_go_snd : (argsResults.go A R is).2 = R ∪ is.results := by
  suffices ∀ A' R',
    (argsResults.go A (R ∪ R') is).snd = R ∪ (argsResults.go A' R' is).snd
  by simp [results, argsResults]; grind
  induction is generalizing A R <;> grind

@[simp, grind =] public theorem results_nil  : results [] = ∅ := by rfl
@[simp, grind =] public theorem results_cons : results (i ;> is) = i.results ∪ is.results := by
  show (argsResults.go ..).snd = _; grind

@[simp, grind =] public theorem results_append {xs ys : InstSeq} :
    results (xs ++ ys) = xs.results ∪ ys.results := by
  induction xs <;> grind

@[grind =] public theorem mem_results_iff : x ∈ is.results ↔ ∃ i ∈ is, x ∈ i.results := by
  induction is <;> grind

@[grind →] public theorem mem_results_of_mem_inst {x : VarId} (hi : i ∈ is) (hx : x ∈ i.results) :
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
public noncomputable def getDef? (v : VarId) : (is : InstSeq) → Option { i // i ∈ is ∧ v ∈ is.results }
  | [] => none
  | i ;> is =>
      open Classical in
      if hi : v ∈ i.results then
        some ⟨i, by grind⟩
      else
        (getDef? v is).map (fun ⟨i, hi⟩ => ⟨i, by grind⟩)

/-- `is.UsesAt y x` is true when `y` is a (transitive) dependency of `x`. -/
@[grind cases]
public inductive UsesAt (is : InstSeq) (y : VarId) : VarId → Prop
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
public def usesAt (x : VarId) (is : InstSeq) : VarSet :=
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
public theorem usesAt_eq_of_not_mem_results {x : VarId} (h : x ∉ is.results) :
    is.usesAt x = ∅ := by
  induction is <;> grind [usesAt]

end Lemmas
end Vars

/-!
## Program Counter

To define the SSA property, we'd like to say that "no two instructions define
the same variable". Just list membership is not sufficient for this.
`∀ i ∈ is, ∀ j ∈ is, ...` doesn't work, as both `i` and `j` could be
instantiated with the same instruction. Similarly, adding `i ≠ j` is not
sufficient either, as the same instruction could occur twice in the sequence.

Thus, we develop a notion of `PC`, program counter (which really is just a `Fin`
index into the sequence), as well as a way to index into the sequence with
a PC.
-/
public section PC
variable {is js : InstSeq}

/--
`is.PC` is the type of program counters of the sequence `is`.

Each program counter `pc : is.PC` uniquely identifies a location of the program.
-/
@[grind cases, grind]
structure PC (is : InstSeq) : Type where
  idx : Nat
  isLt : idx < is.length := by grind

@[grind] def PC.ofFin (i : Fin is.length) : is.PC where
  idx := i.val
  isLt := i.isLt

/-- Get the instruction at the specified location. -/
@[expose] def PC.get (pc : is.PC) : Inst := is[pc.idx]'pc.isLt

section Lemmas

/-! relation to list membership -/

@[grind =]
theorem mem_iff_get : i ∈ is ↔ (∃ pc : is.PC, i = pc.get) := by
  constructor
  · intro h
    obtain ⟨n, _⟩ : ∃ (n : Fin is.length), is[n] = i := List.get_of_mem h
    refine ⟨.ofFin n, ?_⟩
    grind [PC.get]
  · rintro ⟨pc, h⟩
    apply List.mem_of_getElem
    simpa [PC.get] using h.symm

namespace PC

@[grind =_] theorem eq_iff_idx_eq {i j : is.PC} :
    i = j ↔ i.idx = j.idx := by grind

@[ext, grind ext] theorem eq_of_idx_eq {i j : is.PC} :
    i.idx = j.idx → i = j := by grind

/-! cases principle -/

@[grind] def zero {i is} : PC (i ;> is) where idx := 0
@[grind] def succ {i is} (p : PC is) : PC (i ;> is) where idx := p.idx + 1

@[grind =, simp] theorem get_zero : (@zero i is).get = i := by rfl
@[grind =, simp] theorem get_succ (p : PC is) :
    (@p.succ i _).get (is := no_index _) = p.get := by rfl

@[grind =, simp] theorem succ_eq_succ_iff {p q : is.PC} :
    (@p.succ i is) = q.succ ↔ p = q := by grind

@[cases_eliminator, elab_as_elim]
def consCases {motive : PC (i ;> is) → Prop}
    (zero : motive zero)
    (succ : ∀ (p : PC is), motive p.succ)
    (p : PC (i ;> is)) : motive p := by
  cases hp : p.idx
  case zero   => apply cast ?_ zero; grind
  case succ n => apply cast ?_ (succ ⟨n, by grind⟩); grind

/-! append -/
variable {is js : InstSeq}

def appendLeft (p : PC is) : PC (is ++ js) where idx := p.idx
def appendRight (p : PC js) : PC (is ++ js) where idx := p.idx + is.length

@[grind =, simp] theorem idx_appendLeft :
    (@appendLeft is js p).idx = p.idx := by rfl

@[grind =, simp] theorem idx_appendRight :
    (@appendRight is js p).idx = p.idx + is.length := by rfl

@[grind =, simp] theorem get_appendLeft {p : PC is} :
    (@appendLeft is js p).get = p.get := by grind [get]

@[grind =, simp] theorem get_appendRight {p : PC js} :
    (@appendRight is js p).get = p.get := by grind [get]

@[grind =, simp] theorem appendLeft_eq_appendLeft_iff (p q : PC is) :
    (@p.appendLeft is js) = q.appendLeft ↔ p = q := by grind [appendLeft]
@[grind =, simp] theorem appendRight_eq_appendRight_iff (p q : PC js) :
    (@p.appendRight is js) = q.appendRight ↔ p = q := by grind [appendRight]
@[grind ., simp] theorem appendLeft_neq_appendRight (p : PC is) (q : PC js) :
    p.appendLeft ≠ q.appendRight := by grind [appendLeft, appendRight]

/-! cast -/

def cast (h : is = js) (p : PC is) : PC js where idx := p.idx

@[grind =, simp] theorem idx_cast (h : is = js) (p : PC is) :
    (p.cast h).idx = p.idx := by rfl

@[grind =, simp] theorem get_cast (h : is = js) (p : PC is) :
    (p.cast h).get = p.get := by grind [cast]

@[grind =, simp] theorem cast_eq_cast_iff_heq
    {h₁ : is = is'} {p : PC is}
    {h₂ : js = is'} {q : PC js} :
    p.cast h₁ = q.cast h₂ ↔ p ≍ q := by grind [cast]

end PC
end Lemmas

/-! Map PCs of `is` or `js` into `is ++ js`. -/
section OfAppend
variable {is js : InstSeq}

public def PC.ofAppendLeft : is.PC → (is ++ js).PC
  | ⟨idx, isLt⟩ => ⟨idx, by grind⟩

public def PC.ofAppendRight : js.PC → (is ++ js).PC
  | ⟨idx, isLt⟩ => ⟨idx + is.length, by grind⟩

section AppendLemmas

@[simp, grind =] public theorem get_ofAppendLeft :
    (@PC.ofAppendLeft is js p).get = p.get := by
  grind [PC.get, PC.ofAppendLeft]

@[simp, grind =] public theorem get_ofAppendRight :
    (@PC.ofAppendRight is js p).get = p.get := by
  grind [PC.get, PC.ofAppendRight]

end AppendLemmas
end OfAppend

end PC

/-!
## Embedding

Using the notion of program counter, we define what it means to embed one
program in another.
-/
public section Embed

structure EmbedIn (is js : InstSeq) where
  map : is.PC → js.PC
  get_map : ∀ i, (map i).get = i.get
  inj : ∀ i j : is.PC, i ≠ j → i.get.results ≠ ∅ → j.get.results ≠ ∅ → map i ≠ map j

-- `f : is.EmbedIn js` can be used a function
instance {is js : InstSeq} : CoeFun (is.EmbedIn js) (fun _ => is.PC → js.PC) where
  coe f := f.map

section Lemmas

/-! ### Grind Lemmas -/
attribute [grind .] EmbedIn.inj
attribute [grind =, simp] EmbedIn.get_map

end Lemmas

/-!
TODO: we might want some notion of "embedding" one program in another, using PCs.
For example, we could say that `f : is.EmbedIn js` is defined as a function
`is.PC → js.PC` such that `i ≠ j → f i ≠ f j`.

Then, we should show a generic embedding `I.collapse.EmbedIn (C.plug I)`, given
that `C` is complete.
-/

end Embed

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
      → NoShadowing (i ;> is)

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
    NoShadowing (i ;> is) ↔ i.results.Disjoint is.results ∧ NoShadowing is := by grind

@[grind =, simp] theorem noShadowing_append :
    NoShadowing (is ++ js) ↔ is.results.Disjoint js.results ∧ is.NoShadowing ∧ js.NoShadowing := by
  induction is <;> grind

@[grind ., simp] theorem wellFormed_nil : WellFormed Γ [] := by grind
@[grind =, simp] theorem wellFormed_cons :
    WellFormed Γ (i ;> is) ↔
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

/-!
### Program Counter
Let us now characterize `NoShadowing` in terms of a global condition,
using the program counter.
-/
section PC

theorem noShadowing_iff :
    is.NoShadowing ↔ ∀ (i j : is.PC), i ≠ j →
      i.get.results.Disjoint j.get.results := by
  induction is
  case nil => grind
  case cons i is ih =>
    change InstSeq at is
    simp only [noShadowing_cons, ne_eq]
    constructor
    · rintro ⟨hdj, hns⟩
      intro j k
      cases j <;> cases k <;> grind
    · intro h
      and_intros
      · suffices ∀ j ∈ is, i.results.Disjoint j.results by grind
        suffices ∀ j : is.PC, i.results.Disjoint j.get.results by grind
        intro j
        simpa using h .zero j.succ (by grind)
      · suffices ∀ (i j : is.PC), i ≠ j → i.get.results.Disjoint j.get.results by grind
        intro j k hjk
        simpa using h j.succ k.succ (by grind)

end PC

/-! ### Results -/
section ResultLemmas

@[grind <=]
theorem results_disjoint_of_mem_of_noShadowing (hi : i ∈ is) (hj : j ∈ is) (wf : is.NoShadowing) :
    i ≠ j → i.results.Disjoint j.results := by
  induction is <;> grind

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
