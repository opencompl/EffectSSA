module

public import EffectSSA.ProofSketch.Denote
public import EffectSSA.ProofSketch.VarSet
public import EffectSSA.ProofSketch.Inst
public import EffectSSA.ProofSketch.InstSeq

import Batteries.Data.Vector.Lemmas

/-!
# Contextual Equivalence Proof Sketch

This file contains a stand-alone proof sketch that denotational equivalence
implies contextual equivalence, in an SSA-based rewriting setting.

-/

@[expose] public noncomputable section
namespace EffectSSA.ProofSketch

attribute [grind →] NeZero.out

/-!
## Types
-/

/-!
## Pattern
-/

def Pattern (n : Nat) := Vector InstSeq n

/--
A `HoleId n` is the name of a hole in a context which may include at most `n`
distinct holes.
-/
def Hole n := Fin n

namespace Pattern
variable (v : Pattern n)

@[grind =] def toVector (v : Pattern n) : Vector InstSeq n := v
@[grind =] def ofVector (v : Vector InstSeq n) : Pattern n := v

/-! ### Ctors -/

/--
A vector of exactly `n` empty sequences.

This serves as a canonical "junk", or padding, value for out-of-bound
parameters, following the garbage-in-garbage-out principle.
-/
def junk (n : Nat) : Pattern n := Vector.replicate n []

def cast (h : n = m) : Pattern n → Pattern m := Vector.cast h

instance : HAppend (Pattern n) (Pattern m) (Pattern (n + m)) where
  hAppend xs ys := ofVector <| xs.toVector ++ ys.toVector

/-- The empty vector -/
def nil : Pattern 0 := ofVector #v[]

def cons (is : InstSeq) (I : Pattern n) : Pattern (n + 1) :=
  (ofVector <| #v[is] ++ I.toVector).cast (by grind)

def concat (I : Pattern n) (is : InstSeq) : Pattern (n + 1) :=
  I.push is

/-! ### Getters / Destructors -/

def get (i : Nat) (hi : i < n := by grind) : InstSeq :=
  v.toVector[i]

@[grind] abbrev head [NeZero n] : Pattern n → InstSeq := (·.get 0)
def tail [NeZero n] : Pattern n → Pattern (n - 1) := Vector.tail

/-- Take the first `i` elements, padding with junk if `i > n`. -/
def take (i : Nat) : Pattern i :=
  let vs := ofVector <| Vector.take v.toVector i
  (vs ++ junk (i - n)).cast (by grind)

/-! ### Collapse -/

/--
A vector `v` can be collapsed into a single instruction sequence,
by concatenating each constituent sequence `vₖ`, in order.
-/
def collapse (xs : Pattern n) : InstSeq :=
  Vector.foldl (· ++ ·) [] xs.toVector

/-! ### Membership -/

instance : Membership InstSeq (Pattern n) where
  mem I i := ∃ k hk, i = I.get k hk

/-! ### Variables -/

abbrev args (I : Pattern n) := I.collapse.args
abbrev results (I : Pattern n) := I.collapse.results

/-! ### Pattern Lemmas -/
section Lemmas
variable (xs : Pattern n) (ys : Pattern m)

/-! toVector -/
section ToVector

theorem eq_of_toVector_eq (h : v.toVector = w.toVector) : v = w := by
  exact h

@[simp, grind =] theorem toVector_ofVector (v : Vector _ n) : toVector (ofVector v) = v := rfl

@[simp, grind =] theorem toVector_append : toVector (xs ++ ys) = xs.toVector ++ ys.toVector := rfl
@[simp, grind =] theorem toVector_cast : toVector (xs.cast h) = xs.toVector.cast h := rfl

@[simp, grind =] theorem toVector_junk : toVector (junk n) = Vector.replicate n [] := rfl
@[simp, grind =] theorem toVector_nil : toVector nil = #v[] := rfl
@[simp, grind =] theorem toVector_concat : toVector (xs.concat y) = xs.toVector.push y := rfl
@[simp, grind =] theorem toVector_cons :
    toVector (cons x xs) = (#v[x] ++ xs.toVector).cast (by grind) := rfl

@[simp, grind =] theorem toVector_tail [NeZero n] :
    xs.tail.toVector = (xs.toVector.extract 1 n).cast (by grind) := by rfl

end ToVector

/-! ext -/

@[ext]
theorem ext {v w : Pattern n} (h : ∀ i (hi : i < n), v.get i hi = w.get i hi) : v = w := by
  apply Vector.ext
  grind [get, Vector.get_eq_getElem]

/-! get -/
section Get
attribute [local grind =, local simp] get
attribute [local grind ext] ext

@[simp, grind =] theorem get_ofVector (xs : Vector _ n) : (ofVector xs).get i hi = xs[i] := by rfl
@[simp, grind =] theorem get_cast : (xs.cast h).get i hi = xs.get i (by grind) := by rfl

@[simp, grind =] theorem get_append {i : Nat} (hi : i < n + m) :
    (xs ++ ys).get i hi = if hi : i < n then xs.get i else ys.get (i - n) := by
  simp; grind

@[simp, grind =] theorem get_cons {x : InstSeq} {i : Nat} (hi : i < n + 1) :
    (cons x xs).get i hi = if hi : i = 0 then x else xs.get (i - 1) (by grind) := by
  simp; grind

@[simp, grind =] theorem get_concat {y : InstSeq} {i : Nat} (hi : i < n + 1) :
    (xs.concat y).get i hi = if hi : i = n then y else xs.get i := by
  simp; grind

@[simp, grind =] theorem get_junk {k : Nat} {i : Nat} (hi : i < k) :
    (junk k).get i hi = [] := by
  simp

@[simp, grind =] theorem get_tail [NeZero n] (v : Pattern n) {i : Nat} (hi : i < (n - 1)) :
    v.tail.get i hi = v.get (i + 1) (by grind) := by
  simp; grind

@[simp, grind =] theorem get_take (v : Pattern n) (hj : _) :
    (v.take i).get j hj = if _ : j < min i n then v.get j else [] := by
  simp [get, take]; grind [Vector.getElem_extract]

end Get

/-! append -/

@[simp, grind =] theorem nil_append : nil ++ v = v.cast (by grind) := by
  apply eq_of_toVector_eq; simp
@[simp, grind =] theorem append_nil : v ++ nil = v := by rfl

@[simp, grind =]
theorem cons_append : (cons x xs) ++ ys = (cons x (xs ++ ys)).cast (by grind) := by
  ext; grind

@[simp, grind =, grind =_]
theorem append_eq_concat : xs ++ (ofVector #v[y]) = xs.concat y := by
  ext; grind

/-! cast -/

@[simp, grind =] theorem cast_eq (h : n = n) : v.cast h = v := rfl

/-! nil -/

theorem eq_nil (v : Pattern 0) : v = nil := by ext; grind

/-! cons -/

@[simp, grind =]
theorem cons_head_tail [NeZero n] (v : Pattern n) : cons v.head v.tail = v.cast (by grind) := by
  ext; grind

theorem cons_eq_append : (cons x xs) = ((ofVector #v[x]) ++ xs).cast (by grind) := by
  ext; grind

/-! concat -/

@[grind =] theorem concat_nil : nil.concat i = cons i nil := by ext; grind
@[grind =] theorem concat_cons : concat (cons i v) j = cons i (concat v j) := by
  ext; grind

@[simp, grind =]
theorem append_concat : xs ++ (ys.concat y) = (xs ++ ys).concat y := by
  ext; simp; grind

/-! head / tail -/

@[simp, grind =] theorem head_cons : (cons i is).head = i := by grind
@[simp, grind =] theorem tail_cons : (cons i is).tail = is := by ext; grind

/-! take -/

@[simp, grind =] theorem take_zero : v.take 0 = junk 0 := by ext; grind
@[simp, grind =] theorem take_all : v.take n = v := by ext; grind

@[simp, grind =] theorem take_succ [NeZero n] :
    v.take (k + 1) = cons v.head (v.tail.take k) := by
  ext; grind

theorem take_succ_eq_concat (hk : k < n) (v : Pattern n) :
    v.take (k + 1) = (v.take k).concat (v.get k hk) := by
  ext; grind

/-! #### Cases -/
section Cases

@[induction_eliminator, elab_as_elim]
def consRec {motive : ∀ {n}, Pattern n → Sort u}
    (nil : motive nil)
    (cons : ∀ {n}, (i : InstSeq) → (v : Pattern n) → motive v → motive (cons i v) ) :
    ∀ {n} (v : Pattern n), motive v := @fun n v =>
  match n with
  | 0 => _root_.cast (by congr; ext; grind) nil
  | _+1 =>
    let m := cons v.head v.tail (consRec nil cons v.tail)
    _root_.cast (by congr 1; ext; grind) m

@[cases_eliminator, elab_as_elim]
def consCases {motive : ∀ {n}, Pattern n → Sort u}
    (nil : motive nil)
    (cons : ∀ {n}, (i : InstSeq) → (v : Pattern n) → motive (cons i v) ) :
    ∀ {n} (v : Pattern n), motive v :=
  consRec nil (fun i v _ => cons i v)


@[elab_as_elim]
def concatRec {motive : ∀ {n}, Pattern n → Sort u}
    (nil : motive nil)
    (concat : ∀ {n}, (v : Pattern n) → (i : InstSeq) → motive v → motive (concat v i) ) :
    ∀ {n} (v : Pattern n), motive v := @fun n v =>
  match n with
  | 0 => _root_.cast (by congr; ext; grind) nil
  | n+1 =>
    let m := concat (v.take n) (v.get n) (concatRec nil concat _)
    _root_.cast (by congr 1; ext; grind) m

@[elab_as_elim]
def concatCases {motive : ∀ {n}, Pattern n → Sort u}
    (nil : motive nil)
    (concat : ∀ {n}, (v : Pattern n) → (i : InstSeq) →  motive (concat v i) ) :
    ∀ {n} (v : Pattern n), motive v :=
  concatRec nil (fun v i _ => concat v i)

end Cases

/-! #### Collapse -/


@[simp, grind =] theorem collapse_nil (I : Pattern 0) : I.collapse = [] := by cases I; rfl
@[simp, grind =] theorem collapse_concat : (concat xs x).collapse = xs.collapse ++ x := by
  simp [collapse]

@[simp, grind =]
theorem collapse_append : (xs ++ ys).collapse = xs.collapse ++ ys.collapse := by
  induction ys using concatRec
  · simp
  · simp; grind

@[simp, grind =] theorem collapse_cons : (cons x xs).collapse = x ++ xs.collapse := by
  suffices (ofVector #v[x] ++ xs).collapse = x ++ xs.collapse by grind [cons_eq_append]
  suffices (ofVector #v[x]).collapse = x by simpa
  rfl

@[simp, grind =] theorem collapse_cast (h : n = m) : (xs.cast h).collapse = xs.collapse := by rfl

@[simp, grind =] theorem collapse_eq_head (x : Pattern 1) : x.collapse = x.head := by
  cases x with | cons i x =>
  cases x
  rfl


/-! ### Membership -/
section Mem
variable (I : Pattern n)

theorem mem_iff_get : i ∈ I ↔ ∃ k, ∃ (hk : k < n), i = I.get k hk := by rfl
grind_pattern mem_iff_get => i ∈ I, I.get _

theorem mem_iff_get_hole : i ∈ I ↔ ∃ (h : Hole n), i = I.get h.val := by
  simp only [mem_iff_get]
  constructor
  · rintro ⟨k, hk, h⟩; exact ⟨⟨k, hk⟩, h⟩
  · grind

@[grind .] theorem not_mem_nil : i ∉ nil := by grind [mem_iff_get]

@[simp, grind =] theorem mem_concat : (i ∈ I.concat is) ↔ i ∈ I ∨ i = is := by
  simp only [mem_iff_get, get_concat]
  constructor
  · grind
  · rintro (⟨k, hk, rfl⟩ | rfl)
    · refine ⟨k, ?_⟩; grind
    · refine ⟨n, ?_⟩; grind

end Mem

section Results
variable {I : Pattern n} {is : InstSeq} {x : Var}

@[simp, grind =] theorem results_concat :
    (I.concat is).results = I.results ∪ is.results := by grind

@[grind =] theorem mem_results_iff : x ∈ I.results ↔ ∃ is ∈ I, x ∈ is.results := by
  induction I using Pattern.concatRec <;> grind

@[grind →] theorem mem_results_of_mem (his : is ∈ I) (hx : x ∈ is.results) :
    x ∈ I.results := by grind

@[grind →] theorem results_subset_of_mem (h : is ∈ I) :
    is.results ⊆ I.results := by grind

end Results

end Lemmas
end Pattern


/-!
## Semantics
-/
section Semantics

/-! ### Definition -/

/-- `Val` is the type of runtime values -/
axiom Val : Type

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
  /--
  Whether an interpreter error occured (e.g, a reference to an undefined
  variable). This should never happen in well-formed programs.
  -/
  error : Bool := false

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

@[simp, grind =] theorem InstSeq.denote_cons : ⟦i :: is⟧ = fun ρ => ⟦is⟧ (⟦i⟧ ρ) := by rfl

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

@[simp, grind =]
theorem Pattern.denote_concat (I : Pattern n) (is : InstSeq) :
    ⟦I.concat is⟧ = fun ρ => ⟦is⟧ (⟦I⟧ ρ) := by
  induction I
  case nil =>
    have : ⟦Pattern.nil.concat is⟧ = ⟦is⟧ := by rfl
    simp [*]
  case cons i is ih =>
    simp [concat_cons, ih]

/-! results -/
variable {x : Var}

/-- Instructions only modify the registers in their `results` set. -/
@[grind .] axiom Inst.regs_denote_of_not_mem_results (i : Inst) {x : Var} {ρ : SEnv}
    (h : x ∉ i.results) : (⟦i⟧ ρ).regs x = ρ.regs x

@[grind =] theorem InstSeq.regs_denote_of_not_mem_results (h : x ∉ is.results) :
    (⟦is⟧ ρ).regs x = ρ.regs x := by
  induction is generalizing ρ <;> grind

end Properties
end Semantics

/-!
## Environment Equivalence
-/

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
  ∧ ρ.error = η.error
  ∧ (∀ v, P v → ρ.regs v = η.regs v)

/-- If two environments are equivalent on all variables, they are equal. -/
theorem SEnv.eq_of_equivOn {ρ η} : EquivOn (fun _ => True) ρ η → ρ = η := by
  rcases ρ with ⟨ρ_regs, ρ_state, ρ_error⟩
  rcases η with ⟨η_regs, η_state, η_error⟩
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

/-!
## Refinement
-/

axiom State.Refine : State → State → Prop
instance : HasSubset State where Subset := State.Refine

axiom Val.Refine : Val → Val → Prop
instance : HasSubset Val where Subset := Val.Refine

@[grind, grind cases]
inductive Val.Refine? : Option Val → Option Val → Prop
  | some {v₁ v₂} (h : v₁ ⊆ v₂) : Refine? (some v₁) (some v₂)
  | none {v?} : Refine? none v?
instance : HasSubset (Option Val) where
  Subset := Val.Refine?

/--
We say that `ρ` is a sub-environment of `η`, written as `ρ ⊆ η`,
when `ρ` has an error, or:

* `η` is error-free,
* the global state of `ρ` is refined by the global state of `η`,
* for each variable `v` in the domain of `ρ`,
    the value `ρ v` is refined by `η v`.
-/
instance : HasSubset SEnv where
  Subset ρ η := ¬ρ.error →
    ¬η.error
    ∧ ρ.state ⊆ η.state
    ∧ (∀ v, ρ.regs v ⊆ η.regs v)

section RefineLemmas
variable {ρ₁ ρ₂ ρ₃ : SEnv}

@[simp, grind .]
axiom SEnv.refine_refl (ρ : SEnv) : ρ ⊆ ρ

axiom SEnv.refine_trans {ρ₁ ρ₂ ρ₃ : SEnv} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₃ → ρ₁ ⊆ ρ₃

instance : Trans (α := SEnv) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans := SEnv.refine_trans

@[grind →]
axiom SEnv.refine_antisymm {ρ₁ ρ₂ : SEnv} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₁ → ρ₁ = ρ₂

theorem SEnv.eq_iff_refine_refine {ρ₁ ρ₂ : SEnv} :
    ρ₁ = ρ₂ ↔ (ρ₁ ⊆ ρ₂ ∧ ρ₂ ⊆ ρ₁) := by
  grind

/-! #### Congruence Lemmas -/
section RefineCongr

/--
We assume that each instruction's semantics preserves refinement.

In other words, the semantics are *monotone* w.r.t. the refinement relation.
-/
@[grind .] axiom Inst.denote_isRefinedBy_congr (hρ : ρ₁ ⊆ ρ₂) (i : Inst) :
    ⟦i⟧ ρ₁ ⊆ ⟦i⟧ ρ₂

@[grind .] theorem InstSeq.denote_isRefinedBy_congr (hρ : ρ₁ ⊆ ρ₂) (is : InstSeq) :
    ⟦is⟧ ρ₁ ⊆ ⟦is⟧ ρ₂ := by
  induction is generalizing ρ₁ ρ₂
  · simpa
  · grind

@[grind .] theorem Pattern.denote_isRefinedBy_congr (hρ : ρ₁ ⊆ ρ₂) (I : Pattern n) :
    ⟦I⟧ ρ₁ ⊆ ⟦I⟧ ρ₂ := by
  simp [Pattern.denote_eq, InstSeq.denote_isRefinedBy_congr hρ]

end RefineCongr

end RefineLemmas

/-!
## WellFormedness
-/
section WellFormed
namespace InstSeq

/--
`is.WellFormedFor Γ` holds when `is` uses only variables from the set `Γ`,
and correctly observes the SSA property (meaning, no variables are shadowed).

Note that this does NOT check types.
-/
inductive WellFormedFor : (Γ : VarSet) → InstSeq → Prop
  | nil : WellFormedFor Γ []
  | cons :
    i.args ⊆ Γ  →  Γ.Disjoint i.results  →  WellFormedFor (i.results ∪ Γ) is  →
    -------------------------------------------------------------------
    WellFormedFor Γ (i :: is)

/-- `is.WellFormed` holds when `is` is wellformed for the empty set of variables. -/
abbrev WellFormed := WellFormedFor ∅

section Lemmas
variable {i : Inst} {is js : InstSeq}

@[grind ., simp]
theorem wellFormedFor_nil : WellFormedFor Γ [] := by
  grind [WellFormedFor]

@[grind =, simp]
theorem wellFormedFor_cons :
    WellFormedFor Γ (i :: is) ↔
      i.args ⊆ Γ ∧ Γ.Disjoint i.results ∧ is.WellFormedFor (i.results ∪ Γ) := by
  grind [WellFormedFor]

@[grind =, simp]
theorem wellFormedFor_append :
    WellFormedFor Γ (is ++ js) ↔
      is.WellFormedFor Γ ∧ js.WellFormedFor (is.results ∪ Γ) := by
  induction is generalizing Γ <;> grind

/-! results -/

theorem disjoint_results_of_wellFormed :
    is.WellFormedFor Γ → Γ.Disjoint is.results := by
  intro h; induction h <;> simp_all
grind_pattern disjoint_results_of_wellFormed => is.WellFormedFor Γ, is.results

theorem eq_of_not_disjoint_results_of_mem_of_wellFormed {i j : Inst}
    (hi : i ∈ is) (hj : j ∈ is) (wf : is.WellFormedFor Γ) :
    ¬(i.results.Disjoint j.results) → i = j := by
  intro hdj
  obtain ⟨x, hxi, hxj⟩ : ∃ x, x ∈ i.results ∧ x ∈ j.results := by grind
  induction hi generalizing Γ
  case head => grind
  case tail hd is hi ih =>
    change i ∈ is at hi
    have wf : WellFormedFor (hd.results ∪ Γ) is := by grind
    apply ih ?_ wf
    suffices j ≠ hd by grind
    grind
grind_pattern eq_of_not_disjoint_results_of_mem_of_wellFormed =>
  i.results.Disjoint j.results, i ∈ is, j ∈ is, is.WellFormedFor Γ


/-! arguments -/

theorem args_subset_of_wellFormed :
    is.WellFormedFor Γ → is.args ⊆ Γ := by
  intro h; induction h <;> grind
grind_pattern args_subset_of_wellFormed => WellFormedFor Γ, is.args ⊆ Γ

end Lemmas
end InstSeq

/-! ### Pattern -/
namespace Pattern

abbrev WellFormedFor (Γ : VarSet) (I : Pattern n) : Prop := I.collapse.WellFormedFor Γ

end Pattern
end WellFormed

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


@[simp, grind =]
theorem Pattern.eqnLemma_concat :
    (I.concat is).EqnLemma x ρ ↔ I.EqnLemma x ρ ∧ is.EqnLemma x ρ := by
  grind [EqnLemma]

@[simp, grind .] theorem InstSeq.EqnLemma_nil : InstSeq.EqnLemma [] x ρ := by
  grind [InstSeq.EqnLemma]

@[simp, grind =] theorem InstSeq.EqnLemma_cons {i : Inst} {is : InstSeq} :
    InstSeq.EqnLemma (i :: is) x ρ ↔ i.EqnLemma x ρ ∧ is.EqnLemma x ρ := by
  grind [InstSeq.EqnLemma]

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
    (hwf : is.WellFormedFor Γ) (h : is.EqnLemma x ρ) :
    (⟦is⟧ ρ).regs x = ρ.regs x := by
  induction is generalizing Γ ρ
  · rfl
  · grind

/-! idempotence -/

attribute [grind .] Inst.HasEqn.idempotent

/--
If `is.HasEqn`, then evaluating `is` is guaranteed to yield an environment which
satisfies its own equation lemma at any variable.
-/
@[grind =>]
theorem InstSeq.eqnLemma_denote_self (hEqn : is.HasEqn) (hwf : is.WellFormedFor Γ)
    (ρ) :
    is.EqnLemma x (⟦is⟧ ρ) := by
  induction is generalizing Γ ρ <;> grind

@[grind .]
theorem Pattern.eqnLemma_denote_self (hEqn : I.HasEqn) (hwf : I.WellFormedFor Γ) :
    I.EqnLemma x (⟦I.get k hk⟧ ρ) := by
  sorry

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
  ∀ x ∈ (I.get h.val).args,
    ∀ y, y = x ∨ y ∈ (I.usesAt x) → I.EqnLemma y ρ

section Lemmas
open VarSet -- for set builder notation
variable {I : Pattern n}

theorem Pattern.usesAt_eq_of_mem_results (his : is ∈ I) (hx : x ∈ is.results)
    (wf : ∃ Γ, I.WellFormedFor Γ) :
    I.usesAt x = is.args ∪ { z | (∃ y ∈ is.args, z ∈ I.usesAt y) } := by
  sorry
grind_pattern Pattern.usesAt_eq_of_mem_results => I.usesAt x, x ∈ is.results

end Lemmas
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

/-!
### Denotation
-/
section Denote

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

end Denote

/-!
### Plugging
-/
section Plug

def plug (C : MultiContext n) (I : Pattern n) : InstSeq :=
  C.flatMap <| fun i =>
    match i with
    | .inl (i : Inst) => [i]
    | .inr (h : Hole n) => I.get h.val

section Lemmas
variable {C}

@[simp, grind =] theorem plug_nil : plug [] I = [] := rfl

@[simp, grind =] theorem plug_cons_inst (i : Inst) :
    plug (.inl i :: C) I = i :: plug C I := by rfl

@[simp, grind =] theorem plug_cons_hole (h : Hole n) :
    plug (.inr h :: C) I = I.get h.val ++ plug C I := by rfl

@[simp, grind =]
theorem denote_plug : ⟦C.plug I⟧ = ⟦C⟧ (I.get ·.val) := by
  funext ρ
  induction C generalizing ρ
  case nil => simp
  case cons i C ih => cases i <;> grind

@[grind =] theorem mem_plug_iff (i : Inst) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ h, .inr h ∈ C ∧ i ∈ I.get h.val := by
  simp only [plug, List.mem_flatMap]
  constructor
  · grind
  · rintro (_ | ⟨h, _⟩ )
    · grind
    · refine ⟨.inr h, ?_⟩; grind

@[grind =] theorem mem_plug_iff_of_complete (hC : C.Complete) (i : Inst) :
    i ∈ (C.plug I) ↔ (.inl i) ∈ C ∨ ∃ (h : Hole n), i ∈ I.get h.val := by
  grind

@[grind =] theorem mem_results_plug_iff {I : Pattern n} :
    x ∈ (C.plug I).results ↔
      (∃ i, .inl i ∈ C ∧ x ∈ i.results) ∨ (∃ h, .inr h ∈ C ∧ x ∈ (I.get h.val).results) := by
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

@[grind .] theorem wellFormedFor_pattern_of_plug_wellFormedFor (hC : C.Complete) :
    (C.plug I).WellFormedFor Γ → ∃ Δ, I.WellFormedFor Δ := by
  sorry

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
def Pattern.DenRefine (I J : Pattern n) : Prop :=
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
def Pattern.DenEquiv (I J : Pattern n) : Prop :=
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
def Pattern.CtxRefine (I J : Pattern n) : Prop :=
  ∀ (C : MultiContext n), C.Complete →
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed → CJ.WellFormed →
      ⟦CI⟧ {} ⊆ ⟦CJ⟧ {}

/--
Two patterns `I` and `J` are contextually equivalent,
when for any complete context `C` such that `C[I]` and `C[J]` are both
wellformed, `C[I]` is (denotationally) equivalent to `C[J]`.
-/
def Pattern.CtxEquiv (I J : Pattern n) : Prop :=
  ∀ (C : MultiContext n),
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed → CJ.WellFormed →
      ⟦CI⟧ {} = ⟦CJ⟧ {}

end Contextual

/-!
## Main Result for straight-line programs
-/
attribute [grind =] id_eq

open MultiContext (plug)

/--
In the main proof, we will do induction on the context `C`, meaning that the
context considered in the inductive step will be a sub-context of the original
program context.

Within the proof, we will keep track of a residual variable set `Γ`, which has
all variables of the original program considered in previous steps of the
induction, thus we keep the following invariant about `Γ`.
-/
@[grind] private structure Invariant (Γ : VarSet) (C : MultiContext n) (I : Pattern n) (ρ : SEnv) where
  /-- `C.plug I` is well-formed with free variables `Γ`. -/
  wf : (C.plug I).WellFormedFor Γ
  residual : ∀ x ∈ I.results, x ∈ Γ ∨ (∃ h, .inr h ∈ C ∧ x ∈ (I.get h.val).results)
  -- residual : ∀ x ∈ I.results, x ∈ Γ ∨ x ∈ (C.plug I).results
  /--
  If `x ∈ Γ`, then any transitive dependencies of `x` (in `I`) are also
  part of `Γ`.
  -/
  closed : ∀ x ∈ Γ, ∀ y ∈ I.usesAt x, y ∈ Γ
  eqn : ∀ x ∈ Γ, I.EqnLemma x ρ


namespace Invariant
variable {Γ} {C : MultiContext n} {I : Pattern n} {ρ : SEnv} {i : Inst}

private theorem initial (wf : (C.plug I).WellFormed) (hC : C.Complete) : Invariant ∅ C I { } := by
  grind [Pattern.mem_iff_get_hole]

private theorem of_invariant_cons_inst (hI : I.HasEqn := by assumption) :
    Invariant Γ (.inl i :: C) I ρ → Invariant (i.results ∪ Γ) C I (⟦i⟧ ρ) := by
  rintro ⟨wf, residual, closed, eqn⟩
  have : ∀ x ∈ i.results, x ∉ I.results := by
    intro x hx hxI
    have : x ∉ (C.plug I).results := by grind
    obtain ⟨h, hhC, hhx⟩ : ∃ h, Sum.inr h ∈ C ∧ x ∈ (I.get h.val).results := by
      specialize residual x hxI; grind
    grind
  constructor
  · grind
  · grind
  · grind
  · grind

private theorem of_invariant_cons_hole (hI : I.HasEqn := by assumption) :
    Invariant Γ (.inr h :: C) I ρ →
    Invariant ((I.get h.val).results ∪ Γ) C I (⟦I.get h.val⟧ ρ) := by
  rintro ⟨wf, residual, closed, eqn⟩
  let is := I.get h.val
  simp at wf
  have : is.args ⊆ Γ := by grind
  constructor
  · grind
  · grind
  · intro x hx y hy
    by_cases x ∈ Γ; grind
    replace hx : x ∈ is.results := by grind
    · rw [Pattern.usesAt_eq_of_mem_results (is:=is)] at hy
      <;> grind
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
          · intro x (hx : x ∈ is.args)
            have : is.args ⊆ Γ := by grind
            grind
          · intro x (hx : x ∈ js.args)
            have : js.args ⊆ Δ := by grind
            grind
        · apply Invariant.of_invariant_cons_hole hI hCI
        · apply Invariant.of_invariant_cons_hole hJ hCJ

-- /--
-- Proving denotational equivalence is sufficient for showing contextual equivalence.
-- -/
-- theorem Pattern.ctxEquiv_of_denoteEquiv (I J : Pattern n)
--     (hI : I.HasEqn) (hJ : J.HasEqn) (h_denoteEquiv : I.DenEquiv J) :
--     I.CtxEquiv J := by
--   intro C hC CI CJ ρ
--   have : I.DenRefine J ∧ J.DenRefine I := by grind [DenRefine, DenEquiv]
--   apply SEnv.refine_antisymm
--   <;> apply ctxRefine_of_denoteRefine
--   <;> grind
