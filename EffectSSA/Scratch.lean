
import EffectSSA.Semantics.Denote

import Batteries.Data.Vector.Lemmas

noncomputable section

attribute [grind →] NeZero.out

/-!
## Types
-/

axiom Inst : Type

abbrev InstSeq := List Inst

def Pattern n := Vector InstSeq n

def Context n := Vector InstSeq (n + 1)

/-!
## Getters
-/

namespace Context
variable (C : Context n) (C' : Context m)

/--
A context with zero holes.
-/
def nil (C₀ : InstSeq) (h : n = 0) : Context n :=
  #v[C₀].cast (by grind)

@[simp, grind =]
def toVector : Vector InstSeq (n + 1) := C

def concat (C : Context n) (is : InstSeq) : Context (n + 1) :=
  C.push is

def head : InstSeq := Vector.head C
def tail [NeZero n] : Context (n - 1) :=
  (Vector.tail C).cast <| by
    have : n ≠ 0 := NeZero.out
    grind

/--
A vector of exactly `n` empty sequences.

It's primary purpose is to serve as a canonical "junk" value,
which can be used to make the length work for for out-of-bound parameters,
following the garbage-in-garbage-out principle.
-/
def junk (n) : Vector InstSeq n :=
  Vector.replicate n ([] : InstSeq)

/-- Take the _first_ `i+1` sequences (representing the first `i` holes) of a Context. -/
def takeFirst (i : Nat) : Context i :=
  let C := Vector.take C (i + 1)
  (C ++ junk (i-n)).cast (by grind)

def get (i : Nat) (hi : i ≤ n := by grind) : InstSeq :=
  Vector.get C ⟨i, by grind⟩

section Lemmas

@[ext, grind ext]
theorem ext (h : ∀ (i : Nat), (hi : i ≤ n) → C.get i hi = D.get i hi) : C = D := by
  apply Vector.ext
  grind [get, Vector.get_eq_getElem]

/-! nil -/

@[simp, grind =]
theorem get_nil : (nil C₀ h).get i hi = C₀ := by
  obtain rfl : i = 0 := by grind
  simp [nil, get]

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
  simp [head, concat, Vector.head]

/-! take -/

@[simp, grind =] theorem takeFirst_zero : C.takeFirst 0 = nil C.head (by rfl) := by sorry
@[simp, grind =] theorem takeFirst_all : C.takeFirst n = C := by sorry

end Lemmas
end Context

namespace Pattern
variable (I : Pattern n)

/-- The empty pattern -/
@[grind] def nil (h : n = 0) : Pattern n := #v[].cast (by grind)

@[simp, grind =]
def toVector : Vector InstSeq n := I

def cons (is : InstSeq) (I : Pattern n) : Pattern (n + 1) :=
  (#v[is] ++ I.toVector).cast (by grind)

def concat (I : Pattern n) (is : InstSeq) : Pattern (n + 1) :=
  I.push is

def head [NeZero n] : InstSeq := Vector.head I
def tail [NeZero n] : Pattern (n - 1) := Vector.tail I

/--
A pattern of exactly `n` empty sequences.

It's primary purpose is to serve as a canonical "junk" value,
which can be used to make the length work for for out-of-bound parameters,
following the garbage-in-garbage-out principle.
-/
def junk (n) : Vector InstSeq n :=
  Vector.replicate n ([] : InstSeq)

/-- Take the _first_ `i` elements of a pattern. -/
def takeFirst (i : Nat) : Pattern i :=
  let I := Vector.take I i
  (I ++ junk (i-n)).cast (by grind)

def get (i : Nat) (hi : i < n := by grind) : InstSeq :=
  Vector.get I ⟨i, hi⟩

section Lemmas

@[simp, grind =] theorem takeFirst_zero : I.takeFirst 0 = nil rfl := by sorry
@[simp, grind =] theorem takeFirst_all : I.takeFirst n = I := by sorry

@[simp, grind =] theorem takeFirst_succ' [NeZero n] :
  I.takeFirst (k + 1) = cons I.head (I.tail.takeFirst k) := by sorry

end Lemmas
end Pattern

/-!
## Context Plugging
-/
namespace Context

/--
Plug each hole of `C` with the corresponding element of pattern `I`.
-/
def plug (C : Context n) (I : Pattern n) : InstSeq :=
  match n with
  | 0 => C.head
  | _+1 => C.head ++ I.head ++ (C.tail.plug I.tail)

section Lemmas

@[simp, grind =]
theorem plug_zero (C : Context 0) (I : Pattern 0) : C.plug I = C.head := by rfl

@[grind =]
theorem plug_succ (C : Context (n + 1)) (I : Pattern (n + 1)) :
    C.plug I = C.head ++ I.head ++ (C.tail.plug I.tail) := by rfl

@[simp, grind =]
theorem tail_concat_zero (C : Context 0) (Cᵢ : InstSeq) :
    (C.concat Cᵢ).tail = nil Cᵢ rfl := by
  rw [C.eq_nil rfl]
  rfl

@[simp, grind =]
theorem tail_concat_succ (C : Context (n + 1)) (Cᵢ : InstSeq) :
    (C.concat Cᵢ).tail = C.tail.concat Cᵢ := by
  sorry

@[simp, grind =]
theorem concat_plug_concat (C : Context n) (I : Pattern n) (Cᵢ Iᵢ : InstSeq) :
    (C.concat Cᵢ).plug (I.concat Iᵢ) = C.plug I ++ Iᵢ ++ Cᵢ := by
  induction n
  case zero =>
    rw [plug_succ]
    rw [show (I.concat Iᵢ).head = Iᵢ by sorry]
    rw [C.eq_nil rfl]
    simp [nil, concat, tail, head, Vector.head]
  case succ n ih =>
    specialize ih C.tail I.tail
    have : (I.concat Iᵢ).head = I.head := by sorry
    have : (I.concat Iᵢ).tail = I.tail.concat Iᵢ := by sorry
    grind

@[simp, grind =]
theorem plug_take_succ (C : Context n) (I : Pattern n) (i : Nat) (hi : i + 1 < n) :
    (C.takeFirst (i + 1)).plug (I.takeFirst (i + 1))
    = ((C.takeFirst i).plug (I.takeFirst i)) ++ I.get (i + 1) ++ C.get (i + 1) := by
  letI : NeZero (min (i + 1) n) := ⟨by grind⟩
  generalize hC₁ : C.takeFirst i = C₁
  generalize hC₂ : (C.takeFirst (i + 1)) = C₂
  generalize hI₁ : I.takeFirst i = I₁
  generalize hI₂ : (I.takeFirst (i + 1)) = I₂
  replace hC₂ : C₂ ≍ C₁.concat (C.get (i + 1)) := by sorry
  replace hI₂ : I₂ ≍ I₁.concat (I.get (i + 1)) := by sorry
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
A pattern `I` can be collapsed into an instruction sequence,
by concatenating each constituent sequence `Iₖ`, in order.
-/
def Pattern.collapse : Pattern n → InstSeq :=
  Vector.foldl (· ++ ·) []

/--
A pattern is wellformed, if its collapsed sequence is wellformed.
-/
abbrev Pattern.WellFormed (I : Pattern n) : Prop :=
  I.collapse.WellFormed

section Lemmas

@[simp, grind =] theorem collapse_nil : (Pattern.nil h).collapse = [] := by
  simp [Pattern.collapse, Pattern.nil]

end Lemmas

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
A `Pattern` is evaluated by collapsing it into an instruction sequence,
and evaluating that.
-/
instance : Denote (Pattern n) (SEnv → SEnv) where
  denote I := ⟦I.collapse⟧

/-! ### Properties -/
section Properties

theorem InstSeq.denote_eq {is : InstSeq} :
    ⟦is⟧ = is.foldl (fun e i => i.denote e) := by rfl

@[grind =] theorem Pattern.denote_eq {I : Pattern n} :
    ⟦I⟧ = ⟦I.collapse⟧ := by rfl

@[simp, grind =] theorem InstSeq.denote_nil : ⟦[]⟧ = id := by rfl

@[simp, grind =] theorem InstSeq.denote_append (is js : InstSeq) :
    ⟦is ++ js⟧ = fun ρ => ⟦js⟧ (⟦is⟧ ρ) := by
  grind [InstSeq.denote_eq]

@[simp, grind =] theorem Pattern.denote_nil {I : Pattern 0} : ⟦I⟧ = id := by
  sorry

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

instance : Trans (α := SEnv) (· ≈ ·) (· ≈ ·) (· ≈ ·) where
  trans := by sorry

@[simp, grind ., refl]
theorem SEnv.equiv_refl (ρ : SEnv) : ρ ≈ ρ := by
  sorry

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
  simp [Pattern.denote_eq, hi]

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
  simp [Pattern.denote_eq]
  grind

end Lemmas

/-!
## Main Result
-/
attribute [grind =] id_eq

@[simp]
axiom Pattern.denote_cons : ∀ (is : InstSeq) (I : Pattern n),
    ⟦cons is I⟧ = fun ρ => ⟦I⟧ (⟦is⟧ ρ)

@[simp, grind =]
theorem Pattern.denote_concat (I : Pattern n) (is : InstSeq) :
    ⟦I.concat is⟧ = fun ρ => ⟦is⟧ (⟦I⟧ ρ) := by
  sorry

@[grind →]
theorem Context.wellFormed_tail_plug_tail : ∀ (C : Context (n + 1)) (I : Pattern (n + 1)),
    (C.plug I).WellFormed → (C.tail.plug I.tail).WellFormed := by
  sorry

/--
Proving denotational equivalence is sufficient for showing contextual equivalence.
-/
theorem ctxEquiv_of_denoteEquiv (I J : Pattern n)
    (hI : I.Idempotent) (hJ : J.Idempotent)
    (hd : ∀ i ≤ n, ∀ ρ, ⟦I.takeFirst i⟧ ρ ≈ ⟦J.takeFirst i⟧ ρ) :
    I.CtxEquiv J := by
  intro C CI CJ hwf₁ hc₁ hwf₂ hc₂
  subst CI CJ
  clear hc₁ hc₂ -- We don't want the closedness to be captured in the IH

  suffices ∀ {m} (I₁ J₁ : Pattern m),
    (hI₁ : I₁.Idempotent) → (hJ₁ : J₁.Idempotent) →
    (hd : ∀ i ≤ n, ∀ ρ, ⟦I.takeFirst i⟧ (⟦I₁⟧ ρ) ≈ ⟦J.takeFirst i⟧ (⟦J₁⟧ ρ)) →
    ∀ ρ, ⟦C.plug I⟧ (⟦I₁⟧ ρ) ≈ ⟦C.plug J⟧ (⟦J₁⟧ ρ)
  by apply this (.nil rfl) (.nil rfl) <;> grind
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
      calc ⟦I.tail.takeFirst i⟧ (⟦I₁.concat I.head⟧ ρ)
        _ ≈ ⟦I.takeFirst (i+1)⟧ (⟦I₁⟧ ρ) := by simpa using SEnv.equiv_refl _
        _ ≈ ⟦J.takeFirst (i+1)⟧ (⟦J₁⟧ ρ) := by grind
        _ ≈ ⟦J.tail.takeFirst i⟧ (⟦J₁.concat J.head⟧ ρ) := by simpa using SEnv.equiv_refl _
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
 Inst.Defs,
 Inst.FVar,
 Inst.Idempotent,
 Inst.denote,
 Inst.denote_idempotent,
 InstSeq.WellFormed,
 Pattern.denote_cons,
 Quot.sound,
 State.Equiv,
 Val.Equiv]
-/
#guard_msgs in #print axioms ctxEquiv_of_denoteEquiv
