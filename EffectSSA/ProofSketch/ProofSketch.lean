import EffectSSA.ProofSketch.Denote

import Std.Data.HashMap
import Batteries.Data.Vector.Lemmas

/-!
# Contextual Equivalence Proof Sketch

This file contains a stand-alone proof sketch that denotational equivalence
implies contextual equivalence, in an SSA-based rewriting setting.

-/

noncomputable section
namespace EffectSSA.ProofSketch

attribute [grind →] NeZero.out

/-!
## Types
-/

axiom Inst : Type

abbrev InstSeq := List Inst

/-!
## Pattern
-/

def Pattern (n : Nat) := Vector InstSeq n

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

end Lemmas
end Pattern


/-!
## Semantics
-/
section Semantics

/-! ### Definition -/

/-- `Var` is the type of variables -/
axiom Var : Type

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
  regs : Var → Option Val
  /-- The global state, e.g, for memory and UB -/
  state : State
  /--
  Whether an interpreter error occured (e.g, a reference to an undefined
  variable). This should never happen in well-formed programs.
  -/
  error : Bool

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

end Properties
end Semantics

/-!
## Environment Equivalence
-/

axiom Val.Equiv : Val → Val → Prop
instance : HasEquiv Val where Equiv := Val.Equiv

inductive Val.Equiv? : Option Val → Option Val → Prop
| some {v₁ v₂} (h : v₁ ≈ v₂) : Equiv? (some v₁) (some v₂)
| none : Equiv? none none

instance : HasEquiv (Option Val) where
  Equiv := Val.Equiv?

/-- Equivalence of (global) state. -/
axiom State.Equiv : State → State → Prop
instance : HasEquiv State where Equiv := State.Equiv

/--
`EquivOn P ρ η` holds when environments `ρ` and `η` agree on:

* their global state (up to state equivalence),
* their error field, and
* the value assigned to each variable `v` for which `P v` holds (up to value equivalence)
-/
def SEnv.EquivOn (P : Var → Prop) : SEnv → SEnv → Prop := fun ρ η =>
  ρ.state ≈ η.state
  ∧ ρ.error = η.error
  ∧ (∀ v, P v → ρ.regs v ≈ η.regs v)

/--
`Equiv ρ η` holds when `ρ` and `η` agree on:

1) their global state (up to state equivalence),
2) their error field, and
3) the value assigned to each variable `v`

That is, `Equiv` is just an abbreviation for `EquivOn (fun _ => True)`.
-/
abbrev SEnv.Equiv : SEnv → SEnv → Prop := EquivOn (fun _ => True)
instance : HasEquiv SEnv where Equiv := SEnv.Equiv

section Lemmas

/-
TODO: axiomatise the relevant properties of equivalence on states and values,
      then use those axioms to prove the SEnv.equiv_foo assumptions below.
-/

@[simp, grind ., refl]
axiom SEnv.equiv_refl (ρ : SEnv) : ρ ≈ ρ

axiom SEnv.equiv_trans {ρ₁ ρ₂ ρ₃ : SEnv} : ρ₁ ≈ ρ₂ → ρ₂ ≈ ρ₃ → ρ₁ ≈ ρ₃

instance : Trans (α := SEnv) (· ≈ ·) (· ≈ ·) (· ≈ ·) where
  trans := SEnv.equiv_trans

axiom SEnv.equiv_symm {ρ₁ ρ₂ : SEnv} : ρ₁ ≈ ρ₂ → ρ₂ ≈ ρ₁
grind_pattern SEnv.equiv_symm => ρ₁ ≈ ρ₂

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

@[simp, grind .]
axiom SEnv.refine_refl (ρ : SEnv) : ρ ⊆ ρ

axiom SEnv.refine_trans {ρ₁ ρ₂ ρ₃ : SEnv} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₃ → ρ₁ ⊆ ρ₃

instance : Trans (α := SEnv) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans := SEnv.refine_trans

axiom SEnv.refine_of_equiv {ρ₁ ρ₂ : SEnv} : ρ₁ ≈ ρ₂ → ρ₁ ⊆ ρ₂

@[grind →]
axiom SEnv.equiv_of_refine_refine {ρ₁ ρ₂ : SEnv} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₁ → ρ₁ ≈ ρ₂

@[grind =] theorem SEnv.equiv_iff_refine_refine {ρ₁ ρ₂ : SEnv} :
    ρ₁ ≈ ρ₂ ↔ (ρ₁ ⊆ ρ₂ ∧ ρ₂ ⊆ ρ₁) := by
  grind [refine_of_equiv]

@[grind .]
axiom Inst.denote_isRefinedBy_congr (i : Inst) {ρ₁ ρ₂} (hρ : ρ₁ ⊆ ρ₂) :
    ⟦i⟧ ρ₁ ⊆ ⟦i⟧ ρ₂

end RefineLemmas

/-!
## Equation Lemma
-/
section EqnLemma

def Inst.EqnLemma (i : Inst) (ρ : SEnv) : Prop :=
  ⟦i⟧ ρ = ρ

def InstSeq.EqnLemma (is : InstSeq) (ρ : SEnv) : Prop :=
  ∀ i ∈ is, i.EqnLemma ρ

def Pattern.EqnLemma (I : Pattern n) (ρ : SEnv) : Prop :=
  ∀ i, ∀ hi : i < n, (I.get i).EqnLemma ρ

/--
We say that an instruction `i` has a well-behaved equation lemma when:

* validity of the equation lemma is stable under the execution of more instructions, and
* executing `i` is guaranteed to yield an environment that satisfies its
  own equation lemma
-/
structure Inst.HasEqn (i : Inst) : Prop where
  stable : ∀ ρ, i.EqnLemma ρ → ∀ j : Inst, i.EqnLemma (⟦j⟧ ρ)
  idempotent : ∀ ρ, i.EqnLemma (⟦i⟧ ρ)

def InstSeq.HasEqn (is : InstSeq) : Prop :=
  ∀ i ∈ is, i.HasEqn

def Pattern.HasEqn (I : Pattern n) : Prop :=
  ∀ i, ∀ hi : i < n, (I.get i).HasEqn

section Lemmas

/-! structural lemmas -/
section HasEqn
variable (I : Pattern n) (is : InstSeq)

@[simp, grind .]
theorem Pattern.hasEqn_take : I.HasEqn → (I.take k).HasEqn := by
  grind [Pattern.HasEqn, InstSeq.HasEqn]

@[simp, grind =]
theorem Pattern.eqnLemma_concat :
    (I.concat is).EqnLemma ρ ↔ I.EqnLemma ρ ∧ is.EqnLemma ρ := by
  simp only [EqnLemma, get_concat]
  constructor
  · intro h
    and_intros
    · intro i; specialize h i; grind
    · specialize h n; grind
  · grind

@[simp, grind .] theorem InstSeq.EqnLemma_nil : InstSeq.EqnLemma [] ρ := by
  grind [InstSeq.EqnLemma]

@[simp, grind =] theorem InstSeq.EqnLemma_cons {i : Inst} {is : InstSeq} :
    InstSeq.EqnLemma (i :: is) ρ ↔ i.EqnLemma ρ ∧ is.EqnLemma ρ := by
  grind [InstSeq.EqnLemma]

/-! stability -/

attribute [grind =>] Inst.HasEqn.stable

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another instruction `j`.
-/
@[grind =>]
theorem Pattern.eqnLemma_of_eqnLemma_inst (hI : I.HasEqn) :
    I.EqnLemma ρ → ∀ j : Inst, I.EqnLemma (⟦j⟧ ρ) := by
  intro h j k hk i hi
  specialize h k hk i hi
  specialize hI k hk i hi
  grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Pattern.eqnLemma_of_eqnLemma_instSeq (hI : I.HasEqn) :
    I.EqnLemma ρ → ∀ js : InstSeq, I.EqnLemma (⟦js⟧ ρ) := by
  intro hI js
  induction js generalizing ρ
  · exact hI
  · grind

/--
If `I.HasEqn`, then validity of the equation lemma is stable under the execution
another sequence of instructions `js`.
-/
@[grind .]
theorem Inst.eqnLemma_of_eqnLemma_instSeq {i : Inst} (hi : i.HasEqn) :
    i.EqnLemma ρ → ∀ js : InstSeq, i.EqnLemma (⟦js⟧ ρ) := by
  intro hi js
  induction js generalizing ρ
  · exact hi
  · grind

/-! idempotence -/

attribute [grind .] Inst.HasEqn.idempotent

/--
If `is.HasEqn`, then evaluating `is` is guaranteed to yield an environment which
satisfies the equation lemma.
-/
@[grind .]
theorem InstSeq.eqnLemma_denote_self (h : is.HasEqn) (ρ) :
    is.EqnLemma (⟦is⟧ ρ) := by
  induction is generalizing ρ
  case nil => simp
  case cons i is ih =>
    specialize ih (by grind [HasEqn])
    have hi : i.HasEqn := by grind [HasEqn]
    have : i.EqnLemma (⟦is⟧ (⟦i⟧ ρ)) := by
      apply Inst.eqnLemma_of_eqnLemma_instSeq hi
      apply hi.idempotent
    simp [*]

end HasEqn

/-! denote lemmas -/

@[grind →]
theorem InstSeq.denote_of_eqn {is : InstSeq} (h : is.EqnLemma ρ) :
    ⟦is⟧ ρ = ρ := by
  induction is
  case nil => rfl
  case cons i is ih =>
    have : i.EqnLemma ρ := by grind [EqnLemma]
    grind [EqnLemma, Inst.EqnLemma]

@[grind →]
theorem Pattern.denote_of_eqn {I : Pattern n} (h : I.EqnLemma ρ) :
    ⟦I⟧ ρ = ρ := by
  induction I
  case nil => rfl
  case cons is I ih =>
    specialize ih (by grind [EqnLemma])
    have : is.EqnLemma ρ := by simpa using h 0
    grind

end Lemmas
end EqnLemma

/-!
## Multi Context

We define a notion of a context with multiple holes, also called a multi-context,
by naming each hole.
-/

/--
A `HoleId n` is the name of a hole in a context which may include at most `n`
distinct holes.
-/
def Hole n := Fin n

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

end Plug

/-!
### Domination
-/
section Domination

inductive WellDominatedFor : Nat → MultiContext n → Prop
  | inst {C} : WellDominatedFor k C → WellDominatedFor k (.inl i :: C)
  | hole {C} {h : Hole n} :
      h.val = k →
      WellDominatedFor (k + 1) C →
      WellDominatedFor k (.inr h :: C)
  | nil : n = k → WellDominatedFor k []

def WellDominated : MultiContext n → Prop :=
  WellDominatedFor 0

theorem denote_isRefinedBy_of_wellDominated
    {C : MultiContext n} (hC : C.WellDominated)
    (I : Pattern n) (hI : I.HasEqn)
    (J : Pattern n) (hJ : J.HasEqn)
    (hη : ∀ h : Hole n, ∀ ρ η, ρ ⊆ η →
      (I.take h.val).EqnLemma ρ →
      (J.take h.val).EqnLemma η →
      ⟦I.get h.val⟧ ρ ⊆ ⟦J.get h.val⟧ η
    )
    (ρ η : SEnv) (hρη : ρ ⊆ η) :
    ⟦C⟧ (I.get ·.val) ρ ⊆ ⟦C⟧ (J.get ·.val) η := by
  change C.WellDominatedFor 0 at hC
  generalize hk : 0 = k at hC
  have ⟨hρ, hη⟩ : (I.take k).EqnLemma ρ ∧ (J.take k).EqnLemma η := by
    subst hk; simp [Pattern.EqnLemma]
  clear hk
  induction hC generalizing ρ η
  case nil => simpa
  case inst k i C _ ih =>
    have : (I.take k).HasEqn := by grind
    have : (J.take k).HasEqn := by grind
    specialize ih (⟦i⟧ ρ) (⟦i⟧ η)
    grind
  case hole k C h hk hC ih =>
    apply ih <;> grind [Pattern.take_succ_eq_concat, Pattern.HasEqn]

end Domination

end MultiContext

/-!
## Contextual Refinement & Equivalence
-/
section Contextual

/--
A pattern `I` is contextually refined by pattern `J`,
when for any context `C` such that `C[I]` and `C[J]` are both wellformed and
instruction sequences, `C[I]` is (denotationally) refined by `C[J]`.
-/
def Pattern.CtxRefine (I J : Pattern n) : Prop :=
  ∀ (C : MultiContext n), C.WellDominated →
    let CI := C.plug I;
    let CJ := C.plug J;
      ∀ ρ, ⟦CI⟧ ρ ⊆ ⟦CJ⟧ ρ

/--
Two patterns `I` and `J` are contextually equivalent,
when for any context `C` such that `C[I]` and `C[J]` are both wellformed and
instruction sequences, `C[I]` is (denotationally) equivalent to `C[J]`.
-/
def Pattern.CtxEquiv (I J : Pattern n) : Prop :=
  ∀ (C : MultiContext n), C.WellDominated →
    let CI := C.plug I;
    let CJ := C.plug J;
      ∀ ρ, ⟦CI⟧ ρ ≈ ⟦CJ⟧ ρ

section RefineCongr
variable {ρ₁ ρ₂ : SEnv}

@[grind .]
axiom Inst.denote_refine_congr (hρ : ρ₁ ⊆ ρ₂) (i : Inst) : ⟦i⟧ ρ₁ ⊆ ⟦i⟧ ρ₂

@[grind .]
theorem InstSeq.denote_refine_congr (hρ : ρ₁ ⊆ ρ₂) (is : InstSeq) :
    ⟦is⟧ ρ₁ ⊆ ⟦is⟧ ρ₂ := by
  induction is generalizing ρ₁ ρ₂
  · simpa
  · grind

@[grind .]
theorem Pattern.denote_refine_congr (hρ : ρ₁ ⊆ ρ₂) (I : Pattern n) :
    ⟦I⟧ ρ₁ ⊆ ⟦I⟧ ρ₂ := by
  simp [Pattern.denote_eq, InstSeq.denote_refine_congr hρ]

end RefineCongr
end Contextual

/-!
## Main Result for straight-line programs
-/
attribute [grind =] id_eq

/--
Proving denotational refinement is sufficient for showing contextual refinement.
-/
theorem Pattern.ctxRefine_of_denoteRefine (I J : Pattern n)
    (hI : I.HasEqn) (hJ : J.HasEqn)
    (hd : ∀ i, ∀ hi : i < n, ∀ ρ η, ρ ⊆ η →
      (I.take i).EqnLemma ρ → (J.take i).EqnLemma η →
      ⟦I.get i⟧ ρ ⊆ ⟦J.get i⟧ η
    ) :
    I.CtxRefine J := by
  intro C hC CI CJ ρ₀
  simp only [CI, CJ, MultiContext.denote_plug]
  apply MultiContext.denote_isRefinedBy_of_wellDominated <;> grind

/--
Proving denotational equivalence is sufficient for showing contextual equivalence.
-/
theorem Pattern.ctxEquiv_of_denoteEquiv (I J : Pattern n)
    (hI : I.HasEqn) (hJ : J.HasEqn)
    (hd : ∀ i, ∀ hi : i < n, ∀ ρ,
      (I.take i).EqnLemma ρ →
      ⟦I.get i⟧ ρ = ⟦J.get i⟧ ρ
    ) :
    I.CtxEquiv J := by
  intro C hC CI CJ ρ
  apply SEnv.equiv_of_refine_refine
  <;> apply ctxRefine_of_denoteRefine <;> (try assumption) <;> grind

/--
info: 'EffectSSA.ProofSketch.Pattern.ctxRefine_of_denoteRefine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Inst,
 State,
 Val,
 Var,
 Inst.denote,
 Inst.denote_isRefinedBy_congr,
 SEnv.refine_refl,
 State.Refine,
 Val.Refine]
-/
#guard_msgs in #print axioms Pattern.ctxRefine_of_denoteRefine

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
## Denotation
-/
section Denote

structure InterpreterState (n : Nat) extends SEnv where
  holes : HoleEnv n
  program : CFG n
  block : BlockId

inductive TerminatorResult where
  | ret (results : List Val)
  | jump (block : BlockId) (args : List Val)

axiom Terminator.denote : Terminator → SEnv → TerminatorResult
instance : Denote Terminator (SEnv → TerminatorResult) where
  denote t := t.denote

inductive BlockResult n where
  | ret (results : List Val)
  | jump (state : InterpreterState n)

instance : Denote (Block n) (InterpreterState n → BlockResult n) where
  denote b σ :=
    let insts : MultiContext n := b.insts
    let ρ := ⟦insts⟧ σ.holes σ.toSEnv
    match ⟦b.term⟧ ρ with
    | .ret r => .ret r
    | .jump block _args => .jump { σ with toSEnv := ρ, block }

namespace InterpreterState

def initial (program : Program) : InterpreterState 0 where
  regs     := fun _ => none
  state   := .initial
  error   := false
  program := program
  block   := program.entry
  holes := Fin.elim0 -- N.B: there are no holes in a `InterpreterState 0`

def step (σ : InterpreterState n) : BlockResult n :=
  let b? := σ.program.blocks[σ.block]?
  match b? with
  | none => .jump { σ with error := true }
  | some b => ⟦b⟧ σ

/--
`Reachable σ` holds when state `σ` is reachable from the initial for the
contained program `σ.program`.
-/
inductive Reachable : InterpreterState n → Prop where
  | initial {σ} : σ = initial (σ.program) → Reachable σ
  | step {σ δ} :
      Reachable σ         -- if some state `σ` is reachable,
      → ¬σ.error          -- error-free,
      → σ.step = .jump δ  -- and `σ` jumps to `δ`
      → Reachable δ       -- then `δ` is reachable

end InterpreterState
end Denote
