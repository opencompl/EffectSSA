
import Batteries.Data.Vector.Lemmas

noncomputable section

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
variable (C : Context n)

/--
A context with zero holes.
-/
def nil (C₀ : InstSeq) (h : n = 0) : Context n :=
  #v[C₀].cast (by grind)

def head : InstSeq := Vector.head C
def tail [NeZero n] : Context (n - 1) :=
  (Vector.tail C).cast <| by
    have : n ≠ 0 := NeZero.out
    grind

def drop (i : Nat) : Context (n - i) :=
  if h : i ≤ n then
    (Vector.drop C i).cast (by grind)
  else
    nil (C.get 0) (by grind)

def take (i : Nat) : Context (min i n) :=
  Vector.take C (i+1) |>.cast (by grind)

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

/-! drop -/

@[simp]
axiom head_drop : (C.drop n).head = C.head
grind_pattern head_drop => (C.drop n).head

@[simp, grind =] theorem drop_zero : C.drop 0 = C := by simp [drop]
@[simp, grind =] theorem drop_all : C.drop n = nil (C.get 0) (by grind) := by grind

end Lemmas
end Context

namespace Pattern
variable (I : Pattern n)

/-- The empty pattern -/
@[grind] def nil (h : n = 0) : Pattern n := #v[].cast (by grind)

def head [NeZero n] : InstSeq := Vector.head I
def tail [NeZero n] : Pattern (n - 1) := Vector.tail I

def drop (i : Nat) : Pattern (n - i) :=
  Vector.drop I i

def take (i : Nat) : Pattern (min i n) :=
  Vector.take I i

def get (i : Nat) (hi : i < n := by grind) : InstSeq :=
  Vector.get I ⟨i, hi⟩

section Lemmas

@[simp, grind =] theorem drop_zero : I.drop 0 = I := by simp [drop]
@[simp, grind =] theorem drop_all : I.drop n = nil (by grind) := by
  apply Vector.ext; grind

end Lemmas
end Pattern

/-!
## Context Plugging
-/
namespace Context

/--
Plug the first hole of context `C` with instruction sequence `I`.
-/
def plugOne (C : Context (n + 1)) (I : InstSeq) : Context n := .ofFn <| fun
  | 0 => C.get 0 ++ I ++ C.get 1
  | ⟨i+1, _⟩ => C.get (i + 2)

/--
Plug each hole of `C` with the corresponding element of pattern `I`.
-/
def plug (C : Context n) (I : Pattern n) :=
  match n with
  | 0 => C.head
  | _+1 => (C.plugOne I.head).plug I.tail

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

def SEnv.initial : SEnv := ⟨.initial, .initial⟩

axiom Inst.denote : Inst → SEnv → SEnv

/--
An `InstSeq` is evaluated by evaluating each instruction in turn,
threading the environment through.
-/
def InstSeq.denote (is : InstSeq) (e : SEnv) : SEnv :=
  is.foldl (fun e i => i.denote e) e

@[simp, grind] abbrev Pattern.denote (I : Pattern n) : SEnv → SEnv :=
  I.collapse.denote

/-! ### Properties -/
section Properties

@[simp, grind =] theorem InstSeq.denote_nil : InstSeq.denote [] = id := by rfl

@[simp, grind =] theorem InstSeq.denote_append (is js : InstSeq) (e : SEnv) :
    (is ++ js).denote e = js.denote (is.denote e) := by
  grind [InstSeq.denote]

/-!
Semantics are monotone; any variables not defined by an instruction (sequence)
are not modified.
-/

@[grind =>] axiom Inst.denote_monotone {i : Inst} {e : SEnv} {v : Var} :
    ¬(i.Defs v) → (i.denote e).env v = e.env v

@[grind =]
theorem InstSeq.denote_monotone {is : Inst} {e : SEnv} {v : Var} :
    ¬(is.Defs v) → (is.denote e).env v = e.env v := by
  grind


end Properties
end Semantics

/-!
## Denotational Equivalence
-/
section DenEquiv

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

For now, I avoid this question altogether by axiomatizing, rather than defining,
the equivalence.
-/
axiom Env.Equiv : Env → Env → Prop
instance : HasEquiv Env where Equiv := Env.Equiv

/-- Equivalence of (global) state. -/
axiom State.Equiv : State → State → Prop
instance : HasEquiv State where Equiv := State.Equiv

/-- Equivalence of stateful environments. -/
instance : HasEquiv SEnv where
  Equiv e₁ e₂ := e₁.env ≈ e₂.env ∧ e₁.state ≈ e₂.state

/--
Two sequences `is` and `js` are denotationally equivalent,
when the result of evaluating under any environment is equivalent.
-/
@[grind] def InstSeq.DenoteEquiv (is js : InstSeq) : Prop :=
  ∀ e, is.denote e ≈ js.denote e

/--
Two patterns `I` and `J` are denotationally equivalent,
when their collapsed sequences are denotationally equivalent.
-/
@[grind] def Pattern.DenoteEquiv (I J : Pattern n) : Prop :=
  I.collapse |>.DenoteEquiv J.collapse

@[grind →]
axiom InstSeq.denoteEquiv_iff_of_closed {is js : InstSeq} (hi : is.Closed) (hj : js.Closed) :
  is.DenoteEquiv js ↔ is.denote .initial ≈ js.denote .initial

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

/-!
## Main Result
-/

@[simp]
axiom Context.plug_nil : (nil C₀ h).plug I = C₀
grind_pattern Context.plug_nil => (Context.nil C₀ h).plug I

@[simp, grind ., refl]
axiom SEnv.equiv_refl (ρ : SEnv) : ρ ≈ ρ

/--
Proving denotational equivalence is sufficient for showing contextual equivalence.
-/
theorem ctxEquiv_of_denoteEquiv {I J : Pattern n} (hd : I.DenoteEquiv J) : I.CtxEquiv J := by
  intro C CI CJ hwf₁ hc₁ hwf₂ hc₂
  subst CI CJ
  rw [InstSeq.denoteEquiv_iff_of_closed (by assumption) (by assumption)]
  clear hc₁ hc₂ -- We don't want the closedness to be captured in the IH

  suffices ∀ m, m ≤ n →
    (hd : ∀ (ρ : SEnv),
      (I.drop m).denote ((C.take m |>.plug (I.take m)).denote ρ) ≈
      (J.drop m).denote ((C.take m |>.plug (J.take m)).denote ρ)
    ) →
    ((C.drop m).plug (I.drop m)).denote SEnv.initial ≈ ((C.drop m).plug (J.drop m)).denote SEnv.initial
  by
    specialize this 0
    have (C : Context 0) (I : Pattern 0) : C.plug I = C.get 0 := by rfl
    grind
  clear hd
  intro m hm hd

  -- induction m
  if hm_eq : n = m then
    grind
  else
    have : m < n := by grind
    obtain ⟨m, rfl⟩ : ∃ m', m = m' - 1 := ⟨m + 1, by grind⟩



  stop
  induction n
  case zero => rfl
  case succ n ih =>
    unfold Context.plug
    suffices
      (C.head ++ I.head ++ C.tail.plug I.tail).denote .initial = (C.head ++ J.head ++ C.tail.plug J.tail).denote .initial
    by sorry
    let eC := C.head.denote .initial
    let eI := I.head.denote eC
    let eJ := J.head.denote eC
    suffices
      (C.tail.plug I.tail).denote eI = (C.tail.plug J.tail).denote eJ
    by grind
    skip
