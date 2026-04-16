
import EffectSSA.Semantics.Denote

import Batteries.Data.Vector.Lemmas

noncomputable section

attribute [grind →] NeZero.out

/-!
## Types
-/

axiom Inst : Type

abbrev InstSeq := List Inst

/-!
## Vec

Shared underlying representation for both `Context` and `Pattern`:
a length-indexed vector of instruction sequences.
-/

def Vec (n : Nat) := Vector InstSeq n

namespace Vec
variable (v : Vec n)

@[grind =] def toVector (v : Vec n) : Vector InstSeq n := v
@[grind =] def ofVector (v : Vector InstSeq n) : Vec n := v

/-! ### Ctors -/

/--
A vector of exactly `n` empty sequences.

This serves as a canonical "junk", or padding, value for out-of-bound
parameters, following the garbage-in-garbage-out principle.
-/
def junk (n : Nat) : Vec n := Vector.replicate n []

def cast (h : n = m) : Vec n → Vec m := Vector.cast h

instance : HAppend (Vec n) (Vec m) (Vec (n + m)) where
  hAppend xs ys := ofVector <| xs.toVector ++ ys.toVector

/-- The empty vector -/
def nil : Vec 0 := ofVector #v[]

def cons (is : InstSeq) (I : Vec n) : Vec (n + 1) :=
  (ofVector <| #v[is] ++ I.toVector).cast (by grind)

def concat (I : Vec n) (is : InstSeq) : Vec (n + 1) :=
  I.push is

/-! ### Getters / Destructors -/

def head [NeZero n] : Vec n → InstSeq := Vector.head
def tail [NeZero n] : Vec n → Vec (n - 1) := Vector.tail

def get (i : Nat) (hi : i < n := by grind) : InstSeq :=
  Vector.get v ⟨i, hi⟩

/-- Take the first `i` elements, padding with junk if `i > n`. -/
def take (i : Nat) : Vec i :=
  let vs := ofVector <| Vector.take v i
  (vs ++ junk (i - n)).cast (by grind)

/-! ### Alternate -/


/--
A vector `v` can be collapsed into a single instruction sequence,
by concatenating each constituent sequence `vₖ`, in order.
-/
def collapse : Vec n → InstSeq :=
  Vector.foldl (· ++ ·) []

def alternate {n : Nat} (C : Vec n) (I : Vec m) : InstSeq :=
  match n, m with
  | 0, _  => I.collapse
  | _, 0  => C.collapse
  | _+1, _+1 => C.head ++ I.head ++ (C.tail.alternate I.tail)

/-! ### Vec Lemmas -/
section Lemmas
variable (xs : Vec n) (ys : Vec m)

/-! toVector -/

theorem eq_of_toVector_eq (h : v.toVector = w.toVector) : v = w := by
  exact h

@[simp, grind =] theorem toVector_append : toVector (xs ++ ys) = xs.toVector ++ ys.toVector := rfl
@[simp, grind =] theorem toVector_cast : toVector (xs.cast h) = xs.toVector.cast h := rfl

@[simp, grind =] theorem toVector_junk : toVector (junk n) = Vector.replicate n [] := rfl
@[simp, grind =] theorem toVector_nil : toVector nil = #v[] := rfl
@[simp, grind =] theorem toVector_concat : toVector (xs.concat y) = xs.toVector.push y := rfl
@[simp, grind =] theorem toVector_cons :
    toVector (cons x xs) = (#v[x] ++ xs.toVector).cast (by grind) := rfl

/-! ext -/

@[ext, grind ext]
theorem ext {v w : Vec n} (h : ∀ i (hi : i < n), v.get i hi = w.get i hi) : v = w := by
  apply Vector.ext
  grind [get, Vector.get_eq_getElem]

/-! append -/

@[simp, grind =] theorem nil_append : nil ++ v = v.cast (by grind) := by
  apply eq_of_toVector_eq; simp
@[simp, grind =] theorem append_nil : v ++ nil = v := by rfl

@[simp, grind =]
theorem cons_append : (cons x xs) ++ ys = (cons x (xs ++ ys)).cast (by grind) := by
  sorry

@[simp, grind =, grind =_]
theorem append_eq_concat : xs ++ (ofVector #v[y]) = xs.concat y := by
  sorry

/-! get -/

@[simp, grind =] theorem get_cast : (xs.cast h).get i hi = xs.get i (by grind) := rfl

/-! nil -/

theorem eq_nil (v : Vec 0) : v = nil := by ext; grind

/-! cons -/

@[simp, grind =]
theorem cons_head_tail [NeZero n] (v : Vec n) : cons v.head v.tail = v.cast (by grind) := by
  sorry

/-! concat -/

@[grind =]
theorem concat_nil : nil.concat i = cons i nil := by sorry


@[grind =]
theorem concat_cons : concat (cons i v) j = cons i (concat v j) := by
  ext k hk l
  sorry

/-! head / tail -/

@[simp, grind =] theorem head_cons : (cons i is).head = i := by sorry
@[simp, grind =] theorem tail_cons : (cons i is).tail = is := by sorry

/-! take -/

@[simp, grind =] theorem take_zero : v.take 0 = junk 0 := by sorry
@[simp, grind =] theorem take_all : v.take n = v := by sorry

@[simp, grind =] theorem take_succ [NeZero n] :
  v.take (k + 1) = cons v.head (v.tail.take k) := by sorry

/-! #### Cases -/

attribute [grind =] cast_eq

@[induction_eliminator, elab_as_elim]
def consRec {motive : ∀ {n}, Vec n → Sort u}
    (nil : motive nil)
    (cons : ∀ {n}, (i : InstSeq) → (v : Vec n) → motive v → motive (cons i v) ) :
    ∀ {n} (v : Vec n), motive v := @fun n v =>
  match n with
  | 0 => _root_.cast (by congr; grind) nil
  | _+1 =>
    let m := cons v.head v.tail (consRec nil cons v.tail)
    _root_.cast (by congr 1; grind) m

@[cases_eliminator, elab_as_elim]
def consCases {motive : ∀ {n}, Vec n → Sort u}
    (nil : motive nil)
    (cons : ∀ {n}, (i : InstSeq) → (v : Vec n) → motive (cons i v) ) :
    ∀ {n} (v : Vec n), motive v :=
  consRec nil (fun i v _ => cons i v)

/-! #### Collapse -/


@[simp, grind =] theorem collapse_cons : (cons x xs).collapse = x ++ xs.collapse := by sorry
@[simp, grind =] theorem collapse_nil : nil.collapse = [] := by rfl

@[simp, grind =] theorem collapse_cast (h : n = m) : (xs.cast h).collapse = xs.collapse := by rfl

@[simp, grind =] theorem collapse_eq_head (x : Vec 1) : x.collapse = x.head := by
  sorry

/-! #### Alternate -/


@[simp, grind =]
theorem alternate_cast_left (C : Vec n) (I : Vec m) (h : n = n') :
    alternate (C.cast h) I = alternate C I := by
  sorry
@[simp, grind =]
theorem alternate_cast_right (C : Vec n) (I : Vec m) (h : m = m') :
    alternate C (I.cast h) = alternate C I := by
  sorry

@[simp, grind =]
theorem alternate_append
    (C₁ : Vec n₁) (I₁ : Vec m₁) (hn : n₁ = m₁ + 1) (C₂ : Vec n₂) (I₂ : Vec m₂)  :
    alternate (C₁ ++ C₂) (I₁ ++ I₂) = C₁.alternate I₁ ++ (cons [] C₂).alternate I₂ := by
  subst hn
  induction m₁
  case zero =>
    cases C₁ with | cons _ C₁ => cases C₁ with | nil =>
    cases I₁ with | nil =>
    cases m₂ <;> simp [alternate]
  case succ n ih =>
    cases C₁ with | cons c C₁ =>
    cases I₁ with | cons i I₁ =>
    simp [alternate]; grind

@[simp, grind =]
theorem alternate_concat (C : Vec (n + 1)) (I : Vec n) (Cᵢ Iᵢ : InstSeq) :
    alternate (C.concat Cᵢ) (I.concat Iᵢ) = C.alternate I ++ (Iᵢ ++ Cᵢ) := by
  rw [← append_eq_concat, ← append_eq_concat, alternate_append]
  <;> rfl

end Lemmas

end Vec

abbrev Pattern (n : Nat) := Vec n
abbrev Context (n : Nat) := Vec (n + 1)

/-!
## Getters
-/

namespace Context
variable (C D : Context n)

/--
A context with zero holes.
-/
def nil (C₀ : InstSeq) (h : n = 0) : Context n :=
  #v[C₀].cast (by grind)

def tail [NeZero n] : Context (n - 1) :=
  (Vector.tail C).cast <| by
    have : n ≠ 0 := NeZero.out
    grind

/-- Take the _first_ `i+1` sequences (representing the first `i` holes) of a Context. -/
def take (i : Nat) : Context i :=
  Vec.take C (i + 1)

def get (i : Nat) (hi : i ≤ n := by grind) : InstSeq :=
  Vec.get C i (by grind)

section Lemmas

@[ext, grind ext]
theorem ext (h : ∀ (i : Nat), (hi : i ≤ n) → C.get i hi = D.get i hi) : C = D := by
  apply Vec.ext
  intro i hi
  exact h i (by grind)

/-! nil -/

@[simp, grind =]
theorem get_nil : (nil C₀ h).get i hi = C₀ := by
  obtain rfl : i = 0 := by grind
  simp [nil, get, Vec.get]

theorem eq_nil (h : n = 0) (C : Context n) : C = nil (C.head) h := by
  have : C.head = C.get 0 := by rfl
  grind

@[simp, grind =]
theorem nil_eq_nil_iff : nil is h = nil js h ↔ is = js := by
  constructor
  · have eq_nil_head (is) : is = (nil is h).head := by rfl
    grind
  · grind

/-! head -/

@[simp, grind =]
theorem get_zero_eq_head : C.get 0 = C.head := by rfl

/-! cons / concat -/

@[simp, grind =]
theorem head_concat : (C.concat is).head = C.head := by
  sorry

/-! take -/

@[simp, grind =] theorem take_zero : C.take 0 = nil C.head (by rfl) := by sorry
@[simp, grind =] theorem take_all : C.take n = C := by sorry

end Lemmas
end Context

namespace Pattern
variable (I : Pattern n)

/-- The empty pattern -/
@[grind] abbrev nil (h : n = 0) : Pattern n := Vec.nil.cast h.symm

@[simp, grind =]
def toVector : Vector InstSeq n := I

def cons (is : InstSeq) (I : Pattern n) : Pattern (n + 1) :=
  (#v[is] ++ I.toVector).cast (by grind)

abbrev concat : (I : Pattern n) → (is : InstSeq) → Pattern (n + 1) := Vec.concat

def head [NeZero n] : InstSeq := Vector.head I
def tail [NeZero n] : Pattern (n - 1) := Vector.tail I

/-- Take the _first_ `i` elements of a pattern. -/
@[grind, simp] abbrev take (i : Nat) : Pattern i := Vec.take I i

def get (i : Nat) (hi : i < n := by grind) : InstSeq :=
  Vec.get I i hi

end Pattern

/-!
## Context Plugging
-/
namespace Context

/--
Plug each hole of `C` with the corresponding element of pattern `I`.
-/
abbrev plug (C : Context n) (I : Pattern n) : InstSeq :=
  Vec.alternate C I

section Lemmas

@[simp, grind =]
theorem plug_zero (C : Context 0) (I : Pattern 0) : C.plug I = C.head := by
  simp [Vec.alternate]

@[grind =]
theorem plug_succ (C : Context (n + 1)) (I : Pattern (n + 1)) :
    C.plug I = C.head ++ I.head ++ (C.tail.plug I.tail) := by rfl

@[simp, grind =]
theorem concat_plug_concat (C : Context n) (I : Pattern n) (Cᵢ Iᵢ : InstSeq) :
    plug (C.concat Cᵢ) (I.concat Iᵢ) = C.plug I ++ Iᵢ ++ Cᵢ := by
  grind

end Lemmas
end Context

/-!
## WellFormedness
-/

/--
We assume some notion of wellformedness of instruction sequences.
-/
axiom InstSeq.WellFormed : InstSeq → Prop


/--
A pattern is wellformed, if its collapsed sequence is wellformed.
-/
abbrev Pattern.WellFormed (I : Pattern n) : Prop :=
  I.collapse.WellFormed


/-!
## Variables
-/
axiom Var : Type

/-- `i.Defs v` holds when variable `v` is defined by instruction `i`. -/
axiom Inst.Defs : Inst → Var → Prop
/-- `i.FVar v` holds when variable `v` is free in instruction `i`. -/
axiom Inst.FVar : Inst → Var → Prop

/-- An instruction cannot define any of its free variables. -/
axiom Inst.not_fvar_and_defs (i : Inst) (v : Var) :
    ¬(i.FVar v ∧ i.Defs v)
grind_pattern Inst.not_fvar_and_defs => i.FVar v, i.Defs v

/-- `is.Defs v` holds when variable `v` is defined by sequence `is`. -/
@[grind] def InstSeq.Defs (is : InstSeq) (v : Var) : Prop :=
  ∃ i ∈ is, i.Defs v
/-- `is.Defs v` holds when variable `v` is free in `is`. -/
@[grind] def InstSeq.FVar (is : InstSeq) (v : Var) : Prop :=
  ¬(is.Defs v) ∧ ∃ i ∈ is, i.FVar v

/-- `is` is closed if it has no free variables -/
def InstSeq.Closed (is : InstSeq) : Prop :=
  ∀ v, ¬(is.FVar v)

/-!
## Semantics
-/
section Semantics

/-! ### Definition -/
axiom Val : Type
axiom State : Type

axiom State.initial : State

/--
A (pure) environment `ρ : Env` is a partial map from variables to values.
-/
def Env := Var → Option Val

def Env.initial : Env := fun _ => none

/--
A stateful environment `e : SEnv`
bundles a pure environment with a global state.
-/
structure SEnv where
  env : Env
  state : State
  error : Bool

def SEnv.initial : SEnv where
  env := .initial
  state := .initial
  error := false

axiom Inst.denote : Inst → SEnv → SEnv
instance : Denote Inst (SEnv → SEnv) where
  denote := Inst.denote

/--
An `InstSeq` is evaluated by evaluating each instruction in turn,
threading the environment through.
-/
@[default_instance]
instance : Denote InstSeq (SEnv → SEnv) where
  denote is := is.foldl (fun e i => i.denote e)

/--
A `Vec` is evaluated by collapsing it into an instruction sequence,
and evaluating that.
-/
instance : Denote (Vec n) (SEnv → SEnv) where
  denote I := ⟦I.collapse⟧

/-! ### Properties -/
section Properties

theorem InstSeq.denote_eq {is : InstSeq} :
    ⟦is⟧ = is.foldl (fun e i => i.denote e) := by rfl

@[simp, grind =] theorem InstSeq.denote_nil : ⟦[]⟧ = id := by rfl

@[simp, grind =] theorem InstSeq.denote_append (is js : InstSeq) :
    ⟦is ++ js⟧ = fun ρ => ⟦js⟧ (⟦is⟧ ρ) := by
  grind [InstSeq.denote_eq]


@[grind =] theorem Vec.denote_eq {I : Vec n} :
    ⟦I⟧ = ⟦I.collapse⟧ := by rfl

@[simp, grind =] theorem Vec.denote_nil {I : Vec 0} : ⟦I⟧ = id := by
  cases I; rfl

@[simp, grind =]
theorem Vec.denote_cons  (is : InstSeq) (I : Vec n) :
    ⟦cons is I⟧ = fun ρ => ⟦I⟧ (⟦is⟧ ρ) := by
  simp [Vec.denote_eq]

@[simp, grind =]
theorem Vec.denote_concat (I : Vec n) (is : InstSeq) :
    ⟦I.concat is⟧ = fun ρ => ⟦is⟧ (⟦I⟧ ρ) := by
  induction I
  case nil =>
    have : ⟦Vec.nil.concat is⟧ = ⟦is⟧ := by rfl
    simp [*]
  case cons i is ih =>
    simp [concat_cons, ih]


/-!
Semantics are monotone; any variables not defined by an instruction (sequence)
are not modified.
-/

@[grind =>] axiom Inst.denote_monotone {i : Inst} {e : SEnv} {v : Var} :
    ¬(i.Defs v) → (⟦i⟧ e).env v = e.env v

@[grind =]
theorem InstSeq.denote_monotone {is : Inst} {e : SEnv} {v : Var} :
    ¬(is.Defs v) → (⟦is⟧ e).env v = e.env v := by
  grind


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

/--
Equivalence of pure environments;

There is a mayor unresolved question with regards to how this should be defined.
The obvious choice would be that two environments are equivalent when they have
the same domain, and the mapped values for each variable agrees.

Unfortunately, that disregards the fact that some values might be _stale_, in the sense
that the corresponding variable was linear and previously consumed. When comparing
environments, we need to disregard stale variables.
At the same time, to be able to phrase an equation lemma, we might need to
remember stale values. I originally thought we also needed it for idempotency,
but that is not actually true, since we re-compute the values anyway.

For now, we define equivalence as pointwise equivalence of values.
-/
instance : HasEquiv Env where
  Equiv ρ η := ∀ v, ρ v ≈ η v

/-- Equivalence of (global) state. -/
axiom State.Equiv : State → State → Prop
instance : HasEquiv State where Equiv := State.Equiv

/-- Equivalence of stateful environments. -/
instance : HasEquiv SEnv where
  Equiv e₁ e₂ :=
    e₁.env ≈ e₂.env
    ∧ e₁.state ≈ e₂.state
    ∧ e₁.error = e₂.error

section Lemmas

@[simp, grind ., refl]
axiom SEnv.equiv_refl (ρ : SEnv) : ρ ≈ ρ


axiom SEnv.equiv_trans {ρ₁ ρ₂ ρ₃ : SEnv} : ρ₁ ≈ ρ₂ → ρ₂ ≈ ρ₃ → ρ₁ ≈ ρ₃

instance : Trans (α := SEnv) (· ≈ ·) (· ≈ ·) (· ≈ ·) where
  trans := SEnv.equiv_trans

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
We say that `ρ` is a sub-environment of `η`, written as `ρ ⊆ η`, when
* `ρ` and `η` have the same state,
* the domain of `ρ` is a subset of the domain of `η`, and
* for each variable `v` in the domain of `ρ`,
    the value `ρ v` is refined by `η v`.
-/
instance : HasSubset SEnv where
  Subset ρ η := ¬ρ.error →
    ¬η.error ∧ ρ.state ⊆ η.state ∧
    ∀ v, ρ.env v ⊆ η.env v

/-!
## Idempotency
-/

axiom Inst.Idempotent : Inst → Prop

@[simp, grind .]
axiom Inst.denote_idempotent {i : Inst} (hi : i.Idempotent) (C : InstSeq) (ρ) :
    ⟦i⟧ (⟦C⟧ (⟦i⟧ ρ)) = (⟦C⟧ (⟦i⟧ ρ))

@[grind]
def InstSeq.Idempotent (is : InstSeq) : Prop :=
  ∀ i ∈ is, i.Idempotent

@[simp, grind =]
theorem InstSeq.denote_idempotent {is : InstSeq} (his : is.Idempotent)
    (C : InstSeq) (ρ) :
    ⟦is⟧ (⟦C⟧ (⟦is⟧ ρ)) = (⟦C⟧ (⟦is⟧ ρ)) := by
  induction is generalizing C ρ
  case nil => rfl
  case cons i is ih =>
    calc (⟦i :: is⟧ ∘ ⟦C⟧ ∘ ⟦i :: is⟧) ρ
      _ = (⟦is⟧ ∘ ⟦i⟧ ∘ ⟦C⟧ ∘ ⟦is⟧ ∘ ⟦i⟧) ρ := rfl
      _ = (⟦is⟧ ∘ ⟦is ++ C⟧ ∘ ⟦i⟧) ρ := by grind
      _ = (⟦C⟧ ∘ ⟦is⟧) (⟦i⟧ ρ) := by grind

@[grind]
def Pattern.Idempotent (I : Pattern n) : Prop :=
  I.collapse.Idempotent

@[grind →, simp]
theorem Pattern.idempotent_tail {I : Pattern n} [NeZero n] :
    I.Idempotent → I.tail.Idempotent := by
  sorry
@[grind →, simp]
theorem Pattern.idempotent_head {I : Pattern n} [NeZero n] :
    I.Idempotent → I.head.Idempotent := by
  sorry

@[simp, grind =]
theorem Pattern.idempotent_concat {I : Pattern n} (is : InstSeq) :
    (I.concat is).Idempotent ↔ I.Idempotent ∧ is.Idempotent := by
  sorry

@[simp, grind =]
theorem Pattern.denote_idempotent {I : Pattern n} (hi : I.Idempotent)
    (C : InstSeq) (ρ) :
    ⟦I⟧ (⟦C⟧ (⟦I⟧ ρ)) = (⟦C⟧ (⟦I⟧ ρ)) := by
  have hi : I.collapse.Idempotent := hi
  simp [Vec.denote_eq, hi]

/-!
## Denotational Equivalence
-/
section DenEquiv

/--
Two sequences `is` and `js` are denotationally equivalent,
when the result of evaluating under any environment is equivalent.
-/
@[grind] def InstSeq.DenoteEquiv (is js : InstSeq) : Prop :=
  ∀ e, ⟦is⟧ e ≈ ⟦js⟧ e

/--
Two patterns `I` and `J` are denotationally equivalent,
when their collapsed sequences are denotationally equivalent.
-/
@[grind] def Pattern.DenoteEquiv (I J : Pattern n) : Prop :=
  I.collapse |>.DenoteEquiv J.collapse

/--
Two patterns `I` and `J` are contextually equivalent,
when for any context `C` such that `C[I]` and `C[J]` are both wellformed and
closed instruction sequences,
these resulting sequences are denotationally equivalent.
-/
def Pattern.CtxEquiv (I J : Pattern n) : Prop :=
  ∀ (C : Context n),
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed → CI.Closed → CJ.WellFormed → CJ.Closed →
      CI.DenoteEquiv CJ

section Lemmas
variable {ρ₁ ρ₂ : SEnv}

@[grind .]
axiom Inst.denote_eqv_congr (hρ : ρ₁ ≈ ρ₂) (i : Inst) : ⟦i⟧ ρ₁ ≈ ⟦i⟧ ρ₂

@[grind .]
theorem InstSeq.denote_eqv_congr (hρ : ρ₁ ≈ ρ₂) (is : InstSeq) :
    ⟦is⟧ ρ₁ ≈ ⟦is⟧ ρ₂ := by
  sorry

@[grind .]
theorem Pattern.denote_eqv_congr (hρ : ρ₁ ≈ ρ₂) (I : Pattern n) :
    ⟦I⟧ ρ₁ ≈ ⟦I⟧ ρ₂ := by
  simp [Vec.denote_eq]
  grind

end Lemmas

/-!
## Main Result
-/
attribute [grind =] id_eq

@[grind →]
axiom Context.wellFormed_tail_plug_tail : ∀ (C : Context (n + 1)) (I : Pattern (n + 1)),
    (C.plug I).WellFormed → (C.tail.plug I.tail).WellFormed

/--
Proving denotational equivalence is sufficient for showing contextual equivalence.
-/
theorem ctxEquiv_of_denoteEquiv (I J : Pattern n)
    (hI : I.Idempotent) (hJ : J.Idempotent)
    (hd : ∀ i ≤ n, ∀ ρ, ⟦I.take i⟧ ρ ≈ ⟦J.take i⟧ ρ) :
    I.CtxEquiv J := by
  intro C CI CJ hwf₁ hc₁ hwf₂ hc₂
  subst CI CJ
  clear hc₁ hc₂ -- We don't want the closedness to be captured in the IH

  suffices ∀ {m} (I₁ J₁ : Pattern m),
    (hI₁ : I₁.Idempotent) → (hJ₁ : J₁.Idempotent) →
    (hd : ∀ i ≤ n, ∀ ρ, ⟦I.take i⟧ (⟦I₁⟧ ρ) ≈ ⟦J.take i⟧ (⟦J₁⟧ ρ)) →
    ∀ ρ, ⟦C.plug I⟧ (⟦I₁⟧ ρ) ≈ ⟦C.plug J⟧ (⟦J₁⟧ ρ)
  by apply this (.nil rfl) (.nil rfl) <;>
    grind
  clear hd
  induction n <;> (
    intro m I₁ J₁ hI₁ hJ₁ hd ρ
    have hIJ₁ (ρ) : ⟦I₁⟧ ρ ≈ ⟦J₁⟧ ρ := by
      simpa using hd 0 (by grind) _
  )
  case zero => grind
  case succ k ih =>
    specialize ih I.tail J.tail (by grind) (by grind) C.tail (by grind) (by grind)
                    (I₁.concat I.head) (J₁.concat J.head) (by grind) (by grind) <| by
      intro i hi ρ
      calc ⟦I.tail.take i⟧ (⟦I₁.concat I.head⟧ ρ)
        _ ≈ ⟦I.take (i+1)⟧ (⟦I₁⟧ ρ) := by simpa using SEnv.equiv_refl _
        _ ≈ ⟦J.take (i+1)⟧ (⟦J₁⟧ ρ) := by grind
        _ ≈ ⟦J.tail.take i⟧ (⟦J₁.concat J.head⟧ ρ) := by simpa using SEnv.equiv_refl _
    calc
      ⟦C.plug I⟧ (⟦I₁⟧ ρ)
      _ ≈ (⟦C.tail.plug I.tail⟧ ∘ ⟦I.head⟧ ∘ ⟦C.head⟧ ∘ ⟦I₁⟧) ρ := by grind
      _ ≈ (⟦C.tail.plug I.tail⟧ ∘ ⟦I.head⟧ ∘ ⟦I₁⟧ ∘ ⟦C.head⟧ ∘ ⟦I₁⟧) ρ := by grind
      _ ≈ (⟦C.tail.plug I.tail⟧ ∘ ⟦I.head⟧ ∘ ⟦I₁⟧ ∘ ⟦C.head⟧ ∘ ⟦J₁⟧) ρ := by grind
      _ ≈ (⟦C.tail.plug J.tail⟧ ∘ ⟦J.head⟧ ∘ ⟦J₁⟧ ∘ ⟦C.head⟧ ∘ ⟦J₁⟧) ρ := by simpa using ih _
      _ ≈ (⟦C.tail.plug J.tail⟧ ∘ ⟦J.head⟧ ∘ ⟦C.head⟧ ∘ ⟦J₁⟧) ρ := by grind
      _ ≈ ⟦C.plug J⟧ (⟦J₁⟧ ρ) := by grind


/--
info: 'ctxEquiv_of_denoteEquiv' depends on axioms: [Inst,
 State,
 Val,
 Var,
 propext,
 sorryAx,
 Classical.choice,
 Context.wellFormed_tail_plug_tail,
 Inst.Defs,
 Inst.FVar,
 Inst.Idempotent,
 Inst.denote,
 Inst.denote_idempotent,
 InstSeq.WellFormed,
 Quot.sound,
 SEnv.equiv_refl,
 SEnv.equiv_trans,
 State.Equiv,
 Val.Equiv]
-/
#guard_msgs in #print axioms ctxEquiv_of_denoteEquiv
