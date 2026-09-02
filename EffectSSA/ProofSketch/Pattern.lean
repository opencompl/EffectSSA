module

public import EffectSSA.ProofSketch.InstSeq
public import EffectSSA.ProofSketch.Hole

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
def Pattern (ι : Type) (n : Nat) := Vector (InstSeq ι) n

namespace Pattern
variable {ι : Type} {n m : Nat}

@[grind =] def toVector (v : Pattern ι n) : Vector (InstSeq ι) n := v
@[grind =] def ofVector (v : Vector (InstSeq ι) n) : Pattern ι n := v

/-! ### Ctors -/

/--
A vector of exactly `n` empty sequences.

This serves as a canonical "junk", or padding, value for out-of-bound
parameters, following the garbage-in-garbage-out principle.
-/
def junk (n : Nat) : Pattern ι n := Vector.replicate n []

def cast (h : n = m) : Pattern ι n → Pattern ι m := Vector.cast h

instance : HAppend (Pattern ι n) (Pattern ι m) (Pattern ι (n + m)) where
  hAppend xs ys := ofVector (xs.toVector ++ ys.toVector)

/-- The empty vector -/
def nil : Pattern ι 0 := ofVector #v[]

def cons (is : InstSeq ι) (I : Pattern ι n) : Pattern ι (n + 1) :=
  (ofVector (#v[is] ++ I.toVector)).cast (by grind)

/-! ### GetElem -/

instance : GetElem (Pattern ι n) Nat (InstSeq ι) (fun _ i => i < n) where
  getElem I i _ := I.toVector[i]

instance : GetElem (Pattern ι n) (Hole n) (InstSeq ι) (fun _ _ => True) where
  getElem I h _ := I.toVector[h.val]

/-! ### Destructors -/

@[grind] abbrev head [NeZero n] (I : Pattern ι n) : InstSeq ι := I[0]'(by grind)
def tail [NeZero n] : Pattern ι n → Pattern ι (n - 1) := Vector.tail

/-! ### Collapse -/

/--
A vector `v` can be collapsed into a single instruction sequence,
by concatenating each constituent sequence `vₖ`, in order.
-/
def collapse (xs : Pattern ι n) : InstSeq ι :=
  Vector.foldl (· ++ ·) [] xs.toVector

/-! ### Membership -/

instance : Membership (InstSeq ι) (Pattern ι n) where
  mem I i := ∃ (k : Nat) (hk : k < n), i = I[k]

/-! ### Variables -/

noncomputable abbrev args (I : Pattern ι n) := I.collapse.args
noncomputable abbrev results (I : Pattern ι n) := I.collapse.results

/-! ### Pattern Lemmas -/
section Lemmas
variable (xs : Pattern ι n) (ys : Pattern ι m)

/-! toVector -/
section ToVector
@[grind →]
theorem eq_of_toVector_eq {v w : Pattern ι n} (h : v.toVector = w.toVector) : v = w := h

@[simp, grind =] theorem toVector_ofVector (v : Vector (InstSeq ι) n) : toVector (ofVector v) = v := rfl

@[simp, grind =] theorem toVector_append : toVector (xs ++ ys) = xs.toVector ++ ys.toVector := rfl
@[simp, grind =] theorem toVector_cast (h : n = m) : toVector (xs.cast h) = xs.toVector.cast h := rfl

@[simp, grind =] theorem toVector_junk : toVector (junk (ι := ι) n) = Vector.replicate n [] := rfl
@[simp, grind =] theorem toVector_nil : toVector (nil (ι := ι)) = #v[] := rfl
@[simp, grind =] theorem toVector_cons (is : InstSeq ι) (I : Pattern ι n) :
    toVector (cons is I) = (#v[is] ++ I.toVector).cast (by grind) := rfl

@[simp, grind =] theorem toVector_tail [NeZero n] :
    xs.tail.toVector = (xs.toVector.extract 1 n).cast (by grind) := by rfl

end ToVector

/-! ext -/

@[ext]
theorem ext {v w : Pattern ι n} (h : ∀ i (hi : i < n), v[i]'hi = w[i]'hi) : v = w := by
  have : ∀ i (hi : i < n), v.toVector[i] = w.toVector[i] := h
  suffices v.toVector = w.toVector by grind
  apply Vector.ext h

/-! get -/
section Get
attribute [local grind ext] ext

variable (I : Pattern ι n) (hole : Hole n)

@[local simp, local grind =] theorem getElem_eq_getElem_toVector (I : Pattern ι n)
    (i : Nat) (hi : i < n) : I[i]'hi = I.toVector[i] := rfl

@[simp, grind =, grind =_] theorem getElem_hole (I : Pattern ι n) (h : Hole n) :
    I[h] = I[h.val] := by rfl

@[simp, grind =] theorem getElem_ofVector (xs : Vector (InstSeq ι) n) {k} (hk : k < n) :
    (ofVector xs)[k] = xs[k] := by rfl
@[simp, grind =] theorem getElem_cast (h : n = m) {k} (hk : k < m) :
  (xs.cast h)[k]'hk = xs[k] := by rfl

@[simp, grind =] theorem getElem_append {k} (hk : k < n + m) :
    (xs ++ ys)[k] = if hk : k < n then xs[k] else ys[k - n] := by
  simp; grind

@[simp, grind =] theorem getElem_cons {x : InstSeq ι} {i : Nat} (hi : i < n + 1) :
    (cons x xs)[i] = if h : i = 0 then x else xs[i - 1] := by
  simp [cons, Vector.getElem_append]

@[simp, grind =] theorem getElem_junk {k : Nat} {i : Nat} (hi : i < k) :
    (junk k : Pattern ι k)[i] = [] := by
  simp

@[simp, grind =] theorem getElem_tail [NeZero n] (v : Pattern ι n) {i : Nat} (hi : i < (n - 1)) :
    v.tail[i] = v[i + 1] := by
  simp; grind

end Get

/-! append -/
section Append

@[simp, grind =] theorem nil_append (v : Pattern ι n) :
    (nil : Pattern ι _) ++ v = v.cast (by grind) := by
  apply eq_of_toVector_eq; simp

@[simp, grind =] theorem append_nil (v : Pattern ι n) : v ++ (nil : Pattern ι _) = v := by rfl

@[simp, grind =]
theorem cons_append (is : InstSeq ι) (xs : Pattern ι n) (ys : Pattern ι m) :
    (cons is xs) ++ ys = (cons is (xs ++ ys)).cast (by grind) := by
  ext; grind

end Append

/-! cast -/
@[simp, grind =] theorem cast_eq (v : Pattern ι n) (h : n = n) : v.cast h = v := by
  rfl

/-! nil -/

theorem eq_nil (v : Pattern ι 0) : v = nil := by ext; grind

/-! cons -/

@[simp, grind =]
theorem cons_head_tail [NeZero n] (v : Pattern ι n) : cons v.head v.tail = v.cast (by grind) := by
  ext; grind

theorem cons_eq_append : (cons x xs) = ((ofVector #v[x]) ++ xs).cast (by grind) := by
  ext; simp

/-! head / tail -/

@[simp, grind =] theorem head_cons : (cons i is).head = i := by grind
@[simp, grind =] theorem tail_cons {i} {is : Pattern ι n} :
    (cons i is).tail = is := by
  suffices ∀ j (hj : j < n), (cons i is).tail[j] = is[j] by
    apply ext this
  grind

/-! membership -/

@[simp, grind =]
theorem mem_ofVector : is ∈ Pattern.ofVector v ↔ is ∈ v := by
  show (∃ k h, is = v[k]) ↔ is ∈ v
  grind [Vector.mem_iff_getElem]

/-! #### Cases -/
section Cases

@[induction_eliminator, elab_as_elim]
def consRec {motive : ∀ {n}, Pattern ι n → Sort u}
    (nil : motive nil)
    (cons : ∀ {n}, (i : InstSeq ι) → (v : Pattern ι n) → motive v → motive (cons i v) ) :
    ∀ {n} (v : Pattern ι n), motive v := @fun n v =>
  match n with
  | 0 => _root_.cast (by congr; ext; grind) nil
  | _+1 =>
    let m := cons v.head v.tail (consRec nil cons v.tail)
    _root_.cast (by congr 1; ext; grind) m

@[cases_eliminator, elab_as_elim]
def consCases {motive : ∀ {n}, Pattern ι n → Sort u}
    (nil : motive nil)
    (cons : ∀ {n}, (i : InstSeq ι) → (v : Pattern ι n) → motive (cons i v) ) :
    ∀ {n} (v : Pattern ι n), motive v :=
  consRec nil (fun i v _ => cons i v)

end Cases

/-! #### Collapse -/


@[simp, grind =] theorem collapse_nil (I : Pattern ι 0) : I.collapse = [] := by cases I; rfl

open Vector (foldl) in
@[simp, grind =]
theorem collapse_append : (xs ++ ys).collapse = xs.collapse ++ ys.collapse := by
  suffices foldl (· ++ ·) xs.collapse ys.toVector = xs.collapse ++ ys.collapse by simpa [collapse]
  generalize xs.collapse = xs
  induction ys generalizing xs
  case nil => simp [nil]
  case cons y ys ih =>
    show foldl (· ++ ·) xs (#v[y] ++ ys.toVector) = _ ++ foldl (· ++ ·) [] (#v[y] ++ ys.toVector)
    simp [ih]

@[simp, grind =] theorem collapse_cons : (cons x xs).collapse = x ++ xs.collapse := by
  suffices (ofVector #v[x] ++ xs).collapse = x ++ xs.collapse by grind [cons_eq_append]
  suffices (ofVector #v[x]).collapse = x by simpa
  rfl

@[simp, grind =] theorem collapse_cast (h : n = m) : (xs.cast h).collapse = xs.collapse := by rfl

@[grind .] theorem getElem_subset_collapse {I : Pattern ι n} {k : Nat} {hk : k < n} : I[k]'hk ⊆ I.collapse := by
  induction I generalizing k
  · grind
  · cases k <;> grind

@[grind =] theorem length_collapse_tail {I : Pattern ι n} [NeZero n] :
    I.tail.collapse.length = I.collapse.length - I.head.length := by
  suffices I ≍ cons I.head I.tail by grind
  grind

@[grind .] theorem length_getElem_le_length_collapse {I : Pattern ι n} {k : Nat} {hk : k < n} :
    (I[k]'hk).length ≤ I.collapse.length := by
  induction I generalizing k <;> grind

/-! ### Membership -/
section Mem
variable (I : Pattern ι n)

theorem mem_iff_getElem : i ∈ I ↔ ∃ k, ∃ (hk : k < n), i = I[k]'hk := by rfl
grind_pattern mem_iff_getElem => i ∈ I, GetElem.getElem I

theorem mem_iff_getElem_hole : i ∈ I ↔ ∃ (h : Hole n), i = I[h] := by
  simp only [mem_iff_getElem]
  constructor
  · rintro ⟨k, hk, h⟩; exact ⟨⟨k, hk⟩, h⟩
  · grind

@[grind .] theorem not_mem_nil : i ∉ nil := by grind [mem_iff_getElem]

@[simp, grind =] theorem mem_cons : (js ∈ cons is I) ↔ js = is ∨ js ∈ I := by
  simp only [mem_iff_getElem, getElem_cons]
  constructor
  · grind
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · refine ⟨0, ?_⟩; grind
    · refine ⟨k+1, ?_⟩; grind

end Mem

section Results
variable {I : Pattern ι n} {is : InstSeq ι} {x : VarId}

@[grind =] theorem mem_results_iff : x ∈ I.results ↔ ∃ is ∈ I, x ∈ is.results := by
  induction I <;> grind

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

structure PC (I : Pattern ι n) where
  hole : Hole n
  pc : (I[hole]).PC

namespace PC
variable {I : Pattern ι n}

/-! ### Defs -/

@[inherit_doc InstSeq.PC.get]
abbrev get (p : I.PC) : Inst ι := p.pc.get

def ofHeadPC [NeZero n] (p : I.head.PC) : I.PC :=
  ⟨(0 : Fin n), p⟩

def ofTailPC [NeZero n] : I.tail.PC → I.PC
  | ⟨h, p⟩ => ⟨⟨h.val + 1, by grind⟩, ⟨p.idx, by grind⟩⟩

/-- Map a pattern PC into the sequence PC of the collapsed pattern. -/
def collapse : {n : Nat} → {I : Pattern ι n} → (p : I.PC) → I.collapse.PC
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
def ofCollapse {n} {I : Pattern ι n} (p : I.collapse.PC) : I.PC :=
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
  fun_induction collapse
  next => grind
  next n m hn I pc pc₁ pc₂ ih =>
    subst pc₁ pc₂
    rw [InstSeq.PC.get_cast, InstSeq.get_ofAppendRight]
    simp only [Pattern.PC.get] at ih ⊢
    exact ih.trans (InstSeq.PC.get_cast _ pc)

@[simp, grind =] theorem get_ofCollapse {p : I.collapse.PC} : (ofCollapse p).get = p.get := by
  induction n
  · grind
  · cases I
    simp only [ofCollapse]
    split <;> (simp [InstSeq.PC.get, *]; grind)

/-! injectivity -/

@[simp, grind =] theorem ofHeadPC_inj [NeZero n] {p q : I.head.PC} :
    ofHeadPC p = ofHeadPC q ↔ p = q := by
  grind [ofHeadPC]

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

/-! ## Pattern WellFormedness -/
section WellFormed

@[inherit_doc InstSeq.NoShadowing]
abbrev NoShadowing (I : Pattern ι n) := I.collapse.NoShadowing

@[inherit_doc InstSeq.WellFormed]
abbrev WellFormed (Γ : VarSet) (I : Pattern ι n) : Prop := I.collapse.WellFormed Γ

section Lemmas
variable {I : Pattern ι n}

@[simp, grind =]
theorem wellFormed_cons :
    (cons is I).WellFormed Γ ↔ is.WellFormed Γ ∧ I.WellFormed (is.results ∪ Γ) := by
  grind

theorem wellFormed_get_of_wellFormed {k : Nat} {hk : k < n} :
    I.WellFormed Γ → ∃ Δ, (I[k]).WellFormed Δ := by
  induction I generalizing Γ k
  · grind
  · cases k <;> grind
grind_pattern wellFormed_get_of_wellFormed => I.WellFormed Γ, (I[k]).WellFormed _

/-! results -/

theorem results_disjoint_of_mem_of_noShadowing (hi : is ∈ I) (hj : js ∈ I) (wf : I.NoShadowing) :
    is ≠ js → is.results.Disjoint js.results := by
  induction I <;> grind
-- grind_pattern results_disjoint_of_mem_of_wellFormed => is ∈ I, js ∈ I, I.WellFormed
-- grind_pattern results_disjoint_of_mem_of_wellFormed => is ∈ I, js ∈ I, I.WellFormed _

end Lemmas
end WellFormed

/-! ### Straigt-Line Semantics -/
public section Denote
variable [SSA ι σ ν]

/--
A `Pattern` is evaluated by collapsing it into an instruction sequence,
and evaluating that.
-/
instance : Denote (Pattern ι n) (SEnv ι → SEnv ι) where
  denote I := ⟦I.collapse⟧

section Lemmas

@[grind =] theorem denote_eq {I : Pattern ι n} :
    ⟦I⟧ = ⟦I.collapse⟧ := by rfl

@[simp, grind =] theorem denote_nil {I : Pattern ι 0} : ⟦I⟧ = id := by
  cases I; rfl

@[simp, grind =]
theorem denote_cons  (is : InstSeq ι) (I : Pattern ι n) :
    ⟦cons is I⟧ = fun ρ => ⟦I⟧ (⟦is⟧ ρ) := by
  simp [Pattern.denote_eq]

/-- The denotation of a pattern is monotone w.r.t. refinement -/
@[grind .] theorem denote_isRefinedBy_congr {ρ₁ ρ₂ : SEnv ι} (hρ : ρ₁ ⊒ ρ₂) (I : Pattern ι n) :
    ⟦I⟧ ρ₁ ⊒ ⟦I⟧ ρ₂ := by
  simp [Pattern.denote_eq, InstSeq.denote_isRefinedBy_congr hρ]

end Lemmas
end Denote


end Pattern
