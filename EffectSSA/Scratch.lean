
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


@[simp, grind =] theorem collapse_nil : nil.collapse = [] := by rfl
@[simp, grind =] theorem collapse_cons : (cons x xs).collapse = x ++ xs.collapse := by sorry
@[simp, grind =] theorem collapse_concat : (concat xs x).collapse = xs.collapse ++ x := by sorry

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
theorem alternate_cons_succ (C₀ : InstSeq) (C : Vec n) (I : Vec (m+1)) :
    (cons C₀ C).alternate I = C₀ ++ I.head ++ (alternate C I.tail) := by
  simp [alternate]

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
## Context Plugging
-/

/--
Plug each hole of `C` with the corresponding element of pattern `I`.
-/
abbrev Context.plug (C : Context n) (I : Pattern n) : InstSeq :=
  Vec.alternate C I

/-!
## Variables
-/
section Vars

axiom Var : Type

/-- `i.Defs v` holds when variable `v` is defined by instruction `i`. -/
axiom Inst.Defs : Inst → Var → Prop
/-- `i.FVar v` holds when variable `v` is free in instruction `i`. -/
axiom Inst.FVar : Inst → Var → Prop

/-- `is.Defs v` holds when variable `v` is defined by any instruction `i ∈ is`. -/
@[grind] def InstSeq.Defs (is : InstSeq) (v : Var) : Prop :=
  ∃ i ∈ is, i.Defs v

/-- `is.FVar v` holds when variable `v` is free in `is`. -/
@[grind] def InstSeq.FVar (is : InstSeq) (v : Var) : Prop :=
  ¬(is.Defs v) ∧ ∃ i ∈ is, i.FVar v

/-- `is` is closed if it has no free variables -/
def InstSeq.Closed (is : InstSeq) : Prop :=
  ∀ v, ¬(is.FVar v)

@[grind] abbrev Vec.Defs (I : Vec n) (v : Var) : Prop :=
  I.collapse.Defs v

@[grind] abbrev Vec.FVar (I : Vec n) (v : Var) : Prop :=
  I.collapse.FVar v

end Vars

/-!
## WellFormedness
-/

/--
We assume some notion of wellformedness of instruction sequences.
-/
axiom InstSeq.WellFormed : InstSeq → Prop

/--
A vec is wellformed, if its collapsed sequence is wellformed.
-/
abbrev Vec.WellFormed (I : Vec n) : Prop :=
  I.collapse.WellFormed


section Lemmas

@[simp, grind .]
axiom InstSeq.wellFormed_nil : WellFormed []

@[simp, grind .]
axiom InstSeq.wellFormed_cons {i : Inst} {is : InstSeq} :
    WellFormed (i :: is) ↔ (WellFormed is ∧ ∀ v,
      ¬(i.Defs v ∧ is.Defs v)     -- variables must be defined exactly once
      ∧ (is.Defs v → ¬(i.FVar v)) -- variables may not be used before they're defined
    )

@[simp, grind =]
theorem InstSeq.wellFormed_append {is js : InstSeq} :
    WellFormed (is ++ js) ↔ (is.WellFormed ∧ js.WellFormed ∧ ∀ v,
      ¬(is.Defs v ∧ js.Defs v)
      ∧ (js.Defs v → ¬(is.FVar v))
    ) := by
  induction is <;> grind

end Lemmas

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

@[simp, grind =] theorem InstSeq.denote_cons : ⟦i :: is⟧ = fun ρ => ⟦is⟧ (⟦i⟧ ρ) := by rfl

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

section RefineLemmas

@[simp, grind .]
axiom SEnv.refine_refl (ρ : SEnv) : ρ ⊆ ρ

axiom SEnv.refine_trans {ρ₁ ρ₂ ρ₃ : SEnv} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₃ → ρ₁ ⊆ ρ₃

instance : Trans (α := SEnv) (· ⊆ ·) (· ⊆ ·) (· ⊆ ·) where
  trans := SEnv.refine_trans

@[grind .]
axiom SEnv.refine_of_equiv {ρ₁ ρ₂ : SEnv} : ρ₁ ≈ ρ₂ → ρ₁ ⊆ ρ₂

@[grind →]
axiom SEnv.equiv_of_refine_refine {ρ₁ ρ₂ : SEnv} : ρ₁ ⊆ ρ₂ → ρ₂ ⊆ ρ₁ → ρ₁ ≈ ρ₂

@[grind =] theorem SEnv.equiv_iff_refine_refine {ρ₁ ρ₂ : SEnv} :
    ρ₁ ≈ ρ₂ ↔ (ρ₁ ⊆ ρ₂ ∧ ρ₂ ⊆ ρ₁) := by
  grind

end RefineLemmas

/-!
## Idempotency
-/

axiom Inst.Idempotent : Inst → Prop

@[grind] def InstSeq.Idempotent (is : InstSeq) : Prop :=
  ∀ i ∈ is, i.Idempotent

@[grind] def Vec.Idempotent (I : Vec n) : Prop :=
  I.collapse.Idempotent

section Lemmas

/-! denote_idempotent -/

@[simp, grind .]
axiom Inst.denote_idempotent {i : Inst} (hi : i.Idempotent) (C : InstSeq)
    (hc : InstSeq.WellFormed (i :: C))
    (ρ : SEnv) :
    ⟦i⟧ (⟦C⟧ (⟦i⟧ ρ)) = (⟦C⟧ (⟦i⟧ ρ))

@[simp, grind =]
theorem InstSeq.denote_idempotent {is : InstSeq} (his : is.Idempotent)
    (C : InstSeq)
    (hc : InstSeq.WellFormed (is ++ C))
    (ρ) :
    ⟦is⟧ (⟦C⟧ (⟦is⟧ ρ)) = (⟦C⟧ (⟦is⟧ ρ)) := by
  induction is generalizing C ρ
  case nil => rfl
  case cons i is ih =>
    calc (⟦i :: is⟧ ∘ ⟦C⟧ ∘ ⟦i :: is⟧) ρ
      _ = (⟦is⟧ ∘ ⟦i⟧ ∘ ⟦C⟧ ∘ ⟦is⟧ ∘ ⟦i⟧) ρ := rfl
      _ = (⟦is⟧ ∘ ⟦is ++ C⟧ ∘ ⟦i⟧) ρ := by grind
      _ = (⟦C⟧ ∘ ⟦is⟧) (⟦i⟧ ρ) := by grind

@[simp, grind =]
theorem Vec.denote_idempotent {I : Vec n} (hi : I.Idempotent)
    (C : InstSeq) (hC : InstSeq.WellFormed (I.collapse ++ C)) (ρ) :
    ⟦I⟧ (⟦C⟧ (⟦I⟧ ρ)) = (⟦C⟧ (⟦I⟧ ρ)) := by
  simp [Vec.denote_eq]; grind

/-! structural idempotency lemmas -/

@[simp, grind =] theorem InstSeq.idempotent_append {is js : InstSeq} :
    (is ++ js).Idempotent ↔ is.Idempotent ∧ js.Idempotent := by
  grind

@[simp, grind →] theorem Vec.idempotent_tail {I : Vec n} [NeZero n] :
    I.Idempotent → I.tail.Idempotent := by
  cases I using Vec.consCases <;> grind

@[simp, grind →] theorem Vec.idempotent_head {I : Vec n} [NeZero n] :
    I.Idempotent → I.head.Idempotent := by
  cases I using Vec.consCases <;> grind

end Lemmas

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
  ∀ (C : Context n),
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed → CJ.WellFormed →
      ∀ ρ, ⟦CI⟧ ρ ⊆ ⟦CJ⟧ ρ

/--
Two patterns `I` and `J` are contextually equivalent,
when for any context `C` such that `C[I]` and `C[J]` are both wellformed and
instruction sequences, `C[I]` is (denotationally) equivalent to `C[J]`.
-/
def Pattern.CtxEquiv (I J : Pattern n) : Prop :=
  ∀ (C : Context n),
    let CI := C.plug I;
    let CJ := C.plug J;
    CI.WellFormed → CJ.WellFormed →
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
  simp [Vec.denote_eq, InstSeq.denote_refine_congr hρ]

end RefineCongr
end Contextual

/-!
## Main Result
-/
attribute [grind =] id_eq

open Context (plug)
/--
Proving denotational refinement is sufficient for showing contextual refinement.
-/
theorem ctxRefine_of_denoteRefine (I J : Pattern n)
    (hI : I.Idempotent) (hJ : J.Idempotent)
    (hd : ∀ i ≤ n, ∀ ρ, ⟦I.take i⟧ ρ ⊆ ⟦J.take i⟧ ρ) :
    I.CtxRefine J := by
  intro C CI CJ

  suffices ∀ {m} (I₁ J₁ : Pattern m),
    (hI₁ : I₁.Idempotent) → (hwf₁ : (I₁.collapse ++ CI).WellFormed) →
    (hJ₁ : J₁.Idempotent) → (hwf₂ : (J₁.collapse ++ CJ).WellFormed) →
    (hd : ∀ i ≤ n, ∀ ρ, ⟦I.take i⟧ (⟦I₁⟧ ρ) ⊆ ⟦J.take i⟧ (⟦J₁⟧ ρ)) →
    ∀ ρ, ⟦C.alternate I⟧ (⟦I₁⟧ ρ) ⊆ ⟦C.alternate J⟧ (⟦J₁⟧ ρ)
  by intro hwf₁ hwf₂; apply this .nil .nil <;> grind
  clear hd
  subst CI CJ
  induction n <;> (
    intro m I₁ J₁ hI₁ hwf₁ hJ₁ hwf₂ hd ρ
    have hIJ₁ (ρ) : ⟦I₁⟧ ρ ⊆ ⟦J₁⟧ ρ := by
      simpa using hd 0 (by grind) _
  )
  case zero => grind
  case succ k ih =>
    change Vec _ at C
    cases C using Vec.consCases with | cons C₀ C =>
    replace ih : ∀ (ρ : SEnv), ⟦Vec.alternate C I.tail⟧ (⟦I₁.concat I.head⟧ ρ) ⊆ ⟦Vec.alternate C J.tail⟧ (⟦J₁.concat J.head⟧ ρ) := by
      apply ih <;> (try grind)
      · intro i hi ρ
        calc ⟦I.tail.take i⟧ (⟦I₁.concat I.head⟧ ρ)
          _ ⊆ ⟦I.take (i+1)⟧ (⟦I₁⟧ ρ) := by simp
          _ ⊆ ⟦J.take (i+1)⟧ (⟦J₁⟧ ρ) := by grind
          _ ⊆ ⟦J.tail.take i⟧ (⟦J₁.concat J.head⟧ ρ) := by simp
    calc
      ⟦(Vec.cons C₀ C).alternate I⟧ (⟦I₁⟧ ρ)
      _ ⊆ (⟦C.alternate I.tail⟧ ∘ ⟦I.head⟧ ∘ ⟦C₀⟧ ∘ ⟦I₁⟧) ρ := by grind
      _ ⊆ (⟦C.alternate I.tail⟧ ∘ ⟦I.head⟧ ∘ ⟦I₁⟧ ∘ ⟦C₀⟧ ∘ ⟦I₁⟧) ρ := by grind
      _ ⊆ (⟦C.alternate I.tail⟧ ∘ ⟦I.head⟧ ∘ ⟦I₁⟧ ∘ ⟦C₀⟧ ∘ ⟦J₁⟧) ρ := by grind
      _ ⊆ (⟦C.alternate J.tail⟧ ∘ ⟦J.head⟧ ∘ ⟦J₁⟧ ∘ ⟦C₀⟧ ∘ ⟦J₁⟧) ρ := by simpa using ih _
      _ ⊆ (⟦C.alternate J.tail⟧ ∘ ⟦J.head⟧ ∘ ⟦C₀⟧ ∘ ⟦J₁⟧) ρ := by grind
      _ ⊆ ⟦(Vec.cons C₀ C).alternate J⟧ (⟦J₁⟧ ρ) := by grind

/--
Proving denotational equivalence is sufficient for showing contextual equivalence.
-/
theorem ctxEquiv_of_denoteEquiv (I J : Pattern n)
    (hI : I.Idempotent) (hJ : J.Idempotent)
    (hd : ∀ i ≤ n, ∀ ρ, ⟦I.take i⟧ ρ ≈ ⟦J.take i⟧ ρ) :
    I.CtxEquiv J := by
  intro C CI CJ hwf₁ hwf₂ ρ
  have hIJ : ⟦C.plug I⟧ ρ ⊆ ⟦C.plug J⟧ ρ := by
    apply ctxRefine_of_denoteRefine <;> grind
  have hJI : ⟦C.plug J⟧ ρ ⊆ ⟦C.plug I⟧ ρ := by
    apply ctxRefine_of_denoteRefine <;> grind
  grind

/--
info: 'ctxRefine_of_denoteRefine' depends on axioms: [Inst,
 State,
 Val,
 Var,
 propext,
 sorryAx,
 Classical.choice,
 Inst.Defs,
 Inst.FVar,
 Inst.Idempotent,
 Inst.denote,
 Inst.denote_idempotent,
 Inst.denote_refine_congr,
 InstSeq.WellFormed,
 InstSeq.wellFormed_cons,
 InstSeq.wellFormed_nil,
 Quot.sound,
 SEnv.refine_refl,
 SEnv.refine_trans,
 State.Refine,
 Val.Refine]
-/
#guard_msgs in #print axioms ctxRefine_of_denoteRefine
