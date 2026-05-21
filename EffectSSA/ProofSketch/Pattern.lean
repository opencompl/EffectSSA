module

public import EffectSSA.ProofSketch.InstSeq

import Batteries.Data.Vector.Lemmas

/-!
# Pattern
-/
@[expose] public section
namespace EffectSSA.ProofSketch

attribute [grind →] NeZero.out

/--
An `n`-ary pattern consists of exactly `n` instruction sequences;
it is the counterpart of an `n`-ary context, which is to say that an
`n`-ary pattern may be plugged into an `n`-ary context to form a complete
instruction sequence.
-/
def Pattern (n : Nat) := Vector InstSeq n

/--
A `HoleId n` is the name of a hole in a context which may include at most `n`
distinct holes. It therefore also identifies a particular sequence in an
`n`-ary pattern.

A `Hole n` is in some sense a meta-variable.
-/
def Hole n := Fin n
  deriving DecidableEq

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

noncomputable abbrev args (I : Pattern n) := I.collapse.args
noncomputable abbrev results (I : Pattern n) := I.collapse.results

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

@[grind .] theorem get_subset_collapse {I : Pattern n} : I.get k hk ⊆ I.collapse := by
  induction I generalizing k
  · grind
  · cases k <;> grind

@[grind =] theorem length_collapse_tail {I : Pattern n} [NeZero n] :
    I.tail.collapse.length = I.collapse.length - I.head.length := by
  suffices I ≍ cons I.head I.tail by grind
  grind

@[grind .] theorem length_get_le_length_collapse {I : Pattern n} :
    (I.get k hk).length ≤ I.collapse.length := by
  induction I generalizing k <;> grind

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

@[simp, grind =] theorem mem_cons : (js ∈ cons is I) ↔ js = is ∨ js ∈ I := by
  simp only [mem_iff_get, get_cons]
  constructor
  · grind
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · refine ⟨0, ?_⟩; grind
    · refine ⟨k+1, ?_⟩; grind

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

/-! ## Program Counter

We define an analogous notion of a "program counter" in a pattern,
which just bundles a hole variable with a program counter of the corresponding
pattern element.
We then show a bijection between the pattern-PC and the PC of the collapsed
instruction sequence.
-/

structure PC (I : Pattern n) where
  hole : Hole n
  pc : (I.get hole.val).PC

namespace PC
variable {I : Pattern n}

/-! ### Defs -/

@[inherit_doc InstSeq.PC.get]
abbrev get (p : I.PC) : Inst := p.pc.get

def ofHeadPC [NeZero n] (p : I.head.PC) : I.PC :=
  ⟨(0 : Fin n), p⟩

def ofTailPC [NeZero n] : I.tail.PC → I.PC
  | ⟨h, p⟩ => ⟨⟨h.val + 1, by grind⟩, ⟨p.idx, by grind⟩⟩

/-- Map a pattern PC into the sequence PC of the collapsed pattern. -/
def collapse : {n : Nat} → {I : Pattern n} → (p : I.PC) → I.collapse.PC
  | n + 1, I, ⟨⟨0, _⟩, pc⟩ =>
      let pc : (I.head ++ I.tail.collapse).PC := pc.ofAppendLeft
      pc.cast <| by
        suffices I = (cons I.head I.tail) by grind
        grind
  | n + 1, I, ⟨⟨h+1, _⟩, pc⟩ =>
      let pc : I.tail.collapse.PC := collapse ⟨⟨h, by grind⟩, pc.cast (by grind)⟩
      let pc : (I.head ++ I.tail.collapse).PC := pc.ofAppendRight
      pc.cast <| by
        suffices I = (cons I.head I.tail) by grind
        grind

/-- Map a sequence PC of a collapsed pattern back into the pattern PC. -/
def ofCollapse {n} {I : Pattern n} (p : I.collapse.PC) : I.PC :=
  match n with
  | 0 => False.elim <| by grind
  | n + 1 =>
      let m := I.head.length
      if hp : p.idx < m then
        ofHeadPC <| ⟨p.idx, by grind⟩
      else
        ofTailPC <| ofCollapse ⟨p.idx - m, by grind⟩

section CollapseLemmas

/-! get lemmas -/

@[simp, grind =] theorem get_ofHeadPC [NeZero n] {p : I.head.PC} : (ofHeadPC p).get = p.get := by rfl
@[simp, grind =] theorem get_ofTailPC [NeZero n] {p : I.tail.PC} : (ofTailPC p).get = p.get := by
  grind [ofTailPC, PC]

/-! injectivity -/

@[simp, grind =] theorem get_collapse {p : I.PC} : p.collapse.get = p.get := by
  fun_induction collapse <;> grind

@[simp, grind =] theorem get_ofCollapse {p : I.collapse.PC} : (ofCollapse p).get = p.get := by
  induction n
  · grind
  · cases I
    simp only [ofCollapse]
    split <;> (simp [InstSeq.PC.get, *]; grind)

/-! injectivity -/

@[simp, grind =] theorem ofHeadPC_inj [NeZero n] {p q : I.head.PC} :
    ofHeadPC p = ofHeadPC q ↔ p = q := by
  simp [ofHeadPC, InstSeq.PC.eq_iff_idx_eq]

@[simp, grind =] theorem ofTailPC_inj [NeZero n] {p q : I.tail.PC} :
    ofTailPC p = ofTailPC q ↔ p = q := by
  grind [ofTailPC, PC]

@[simp, grind .] theorem ofHeadPC_ne_ofTailPC [NeZero n]
    (p : I.head.PC) (q : I.tail.PC) : ofHeadPC p ≠ ofTailPC q := by
  grind [ofHeadPC, ofTailPC, PC]

@[simp, grind =] theorem ofCollapse_inj {p q : I.collapse.PC} :
    ofCollapse p = ofCollapse q ↔ p = q := by
  induction n <;> (simp [ofCollapse]; grind)

end CollapseLemmas

end PC
end Pattern
