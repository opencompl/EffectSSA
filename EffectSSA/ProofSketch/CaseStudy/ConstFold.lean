module

public import EffectSSA.ProofSketch.ProofSketch
public import EffectSSA.ProofSketch.Rewrite
public import EffectSSA.ProofSketch.InstArr
public import EffectSSA.ProofSketch.Tactic

namespace EffectSSA.ProofSketch
public section

namespace CaseStudy.ConstFold

inductive SimpleArith
  /-- `$n` -/
  | const (n : Nat)
  | add
  deriving DecidableEq

instance : SSA SimpleArith Unit Nat where
  initialState := ()
  instDenote := {
    denote i _ xs := ((), match i, xs with
      | .const n, [] => [n]
      | .add, [x, y] => [x + y]
      | _, _ => []
    )
  }

/-- `$x := $n` -/
abbrev constOp (x : VarId) (n : Nat) : Inst SimpleArith where
  results := [x]
  opCode := .const n
  args := []

/-- `$x := add($y, $z)` -/
abbrev addOp (x y z : VarId) : Inst SimpleArith where
  results := [x]
  opCode := .add
  args := [y, z]

@[simp] theorem results_constOp : (constOp x n).results = [x] := by rfl
@[simp] theorem args_constOp : (constOp x n).args = [] := by rfl

@[simp] theorem resultsSet_constOp : (constOp x n).resultsSet = {x} := by
  ext; simp
@[simp] theorem argsSet_constOp : (constOp x n).argsSet = ∅ := by
  ext; simp

@[simp] theorem results_addOp : (addOp x y z).results = [x] := by rfl
@[simp] theorem args_addOp : (addOp x y z).args = [y, z] := by rfl

@[simp] theorem resultsSet_addOp : (addOp x y z).resultsSet = {x} := by
  ext; simp
@[simp] theorem argsSet_addOp : (addOp x y z).argsSet = {y, z} := by
  ext; simp

/-! ## Semantics Simplification -/

@[simp, grind =] theorem denote_constOp :
    ⟦constOp x c⟧ ρ = { ρ with locals := ρ.locals.with x c } := by
  simp [(⟦·⟧)]

@[simp, grind =] theorem denote_addOp :
    ⟦addOp x y z⟧ ρ = (SEnv.getD <| do
      let y ← ρ.locals y
      let z ← ρ.locals z
      return { ρ with locals := ρ.locals.with x (y + z) }) := by
  simp only [Denote.denote, List.mapM_cons, List.mapM_nil, Option.pure_def, Option.bind_eq_bind,
    Option.bind_some]
  cases ρ.locals y; simp
  cases ρ.locals z <;> simp

/-! ## WellBehavedness -/

/--
All instructions of `SimpleArith` are pure, and thus well-behaved.
-/
@[simp, grind .]
axiom wellbehaved (i : Inst SimpleArith) : i.HasEqn

/-! ## Rewrite Family & Soundness -/

/-- `$x := $c₁; $y := $c₂; $z := add($x, $y)` ⟹ `...; $z := ${c₁ + c₂}` -/
@[expose] def constFoldRw (x y z : VarId) (c₁ c₂ : Nat) : Rewrite SimpleArith 3 where
  src := .ofVector #v[
    [constOp x c₁],
    [constOp y c₂],
    [addOp z x y]
  ]
  tgt := .ofVector #v[
    [constOp x c₁],
    [constOp y c₂],
    [constOp z (c₁ + c₂)],
  ]
  wellbehaved_src := by grind
  wellbehaved_tgt := by grind

/-- `$x := $c₁; $z := add($x, $x)` ⟹ `...; $z := ${c₁ + c₁}` -/
@[expose] def constFoldRwAlt (x z : VarId) (c₁ : Nat) : Rewrite SimpleArith 2 where
  src := .ofVector #v[
    [constOp x c₁],
    [addOp z x x]
  ]
  tgt := .ofVector #v[
    [constOp x c₁],
    [constOp z (c₁ + c₁)],
  ]
  wellbehaved_src := by grind
  wellbehaved_tgt := by grind

/-!
`constFoldRwAlt` seems a bit duplicated, it is really just a specialization of `constFoldRw`.
The need for it arises from our definition of "completeness" of a context, which currently
states that a context must contain *all* holes.

In our case, if we have a rewrite like `constFoldRw x y y c c`, then the first
and second hole are identical, thus this rewrite would be perfectly safe to
apply in a context which does not mention (at most) one of the first or second
hole. In fact, if we wanted to apply this rewrite in a real program, then both
"hole"s really just refer to the exact same instruction, and thus only one of
the hole *can* even be mentionened.

Thus `constFoldRwAlt` exists, which has just the one constant.

Ideally, though, we would like to say that for that particular instance of the
3-ary rewrite `constFoldRw`, the notion of completeness is a bit more relaxed
to be able to use that one as-is.
-/

@[simp, grind .]
theorem constFoldRw.isSound : (constFoldRw x y z c₁ c₂).IsSound := by
  simp only [Rewrite.IsSound, Pattern.DenRefine, Pattern.getElem_hole]
  rintro ⟨_|_|_⟩ ρ η hρη
  · suffices ⟦constOp x c₁⟧ ρ ⊒ ⟦constOp x c₁⟧ η by
      rintro - -; simpa [constFoldRw]
    grind
  · suffices ⟦constOp y c₂⟧ ρ ⊒ ⟦constOp y c₂⟧ η by
      rintro - -; simpa [constFoldRw]
    grind
  · rintro h -
    have ⟨hx, hy⟩ : ρ.locals x = some c₁ ∧ ρ.locals y = some c₂ := by
      reduceEqnLemmaUpTo [constFoldRw] at h
    suffices ⟦addOp z x y⟧ ρ ⊒ ⟦constOp z (c₁ + c₂)⟧ η by simpa [constFoldRw]
    grind

@[simp, grind .]
theorem constFoldRwAlt.isSound : (constFoldRwAlt x z c₁).IsSound := by
  simp only [Rewrite.IsSound, Pattern.DenRefine, Pattern.getElem_hole]
  rintro ⟨_|_⟩ ρ η hρη
  · suffices ⟦constOp x c₁⟧ ρ ⊒ ⟦constOp x c₁⟧ η by
      rintro - -; simpa [constFoldRw]
    grind
  · rintro h -
    have hx : ρ.locals x = some c₁ := by
      replace h : (constFoldRwAlt x z c₁).src.EqnLemma x ρ := by
        simp [constFoldRwAlt, Pattern.EqnLemmaUpTo] at h
        grind [constFoldRwAlt]
      simp only [Pattern.EqnLemma] at h
      specialize h [constOp x c₁] (by simp [constFoldRwAlt])
      grind [Inst.EqnLemma]
    suffices ⟦addOp z x x⟧ ρ ⊒ ⟦constOp z (c₁ + c₁)⟧ η by simpa [constFoldRwAlt]
    grind

/-! ## Implementation -/

abbrev Program := InstArr SimpleArith

/-! ### Matchers -/

/--
`is.matchConst x` returns `some n` if the instruction that defines
variable `x` in `is` is a constant with value `n` (i.e, `constOp x n`).
-/
def Program.matchConst (is : Program) (x : VarId) : Option Nat :=
  go is.toSeq
where go : List (Inst SimpleArith) → Option Nat
  | [] => none
  | { opCode := .const n, args := [], results := [x'] } :: is =>
      if x = x' then some n else go is
  | _ :: is => go is

/-- `matchAdd i` returns `some (x, y, z)` if `i` is a (well-formed) addition
instruction, with `x` as the resulting variable and arguments `y` and `z`.
That is, if `i` is equal to `addOp x y z`. -/
def matchAdd : Inst SimpleArith → Option (VarId × VarId × VarId)
  | { opCode := .add, args := [y, z], results := [x] } => some (x, y, z)
  | _ => none

@[simp, grind =] theorem matchAdd_eq_some_iff :
    matchAdd i = some r ↔ i = addOp r.1 r.2.1 r.2.2 := by
  simp [matchAdd, addOp]; grind

open Program in
@[grind →]
theorem constOp_mem_of_matchConst_eq_some {acc : Program} :
    acc.matchConst x = some c → constOp x c ∈ acc.toSeq := by
  rcases acc with ⟨⟨is⟩⟩
  simp only [matchConst, InstArr.toSeq]
  fun_induction matchConst.go x is <;> grind

/-! ### ConstFold -/

/--
`constFold is` returns an equivalent program, after a constant-folding pass.
-/
@[expose]
def constFold (is : Program) : Program :=
  go (.emptyWithCapacity is.size) is.toSubarray
where
  /--
  `foldInst? acc i` attempts to constant fold instruction `i` (referring to
  `acc` for the instructions that define `i`'s arguments), or returns `none`
  if `i` is not a well-formed, constant-foldable `add` instruction.
  -/
  foldInst? (acc : Program) (i : Inst SimpleArith) : Option (Inst SimpleArith) :=
    do
    let (x, y, z) ← matchAdd i
    let c₁ ← acc.matchConst y
    let c₂ ← acc.matchConst z
    return constOp x (c₁ + c₂)
  /--
  `foldInst acc i` attempts to constant fold instruction `i` with `foldInst?`,
  returning the original instruction unchanged if constant folding failed
  for any reason.
  -/
  foldInst acc i := (foldInst? acc i).getD i
  go (acc : Program) (is : InstSubarray SimpleArith) : Program :=
    if _ : is.size = 0 then
      acc
    else
      let i := foldInst acc is[0]
      go (acc.push i) is.popFront
  termination_by is.size

section FoldInstLemmas
variable {acc : Program} {i : Inst SimpleArith}

@[simp, grind =]
theorem constFold.foldInst?_eq_some_iff :
    foldInst? acc i = some i' ↔ ∃ x y z,
      i = addOp x y z
      ∧ ∃ c₁, acc.matchConst y = some c₁
      ∧ ∃ c₂, acc.matchConst z = some c₂
      ∧ i' = constOp x (c₁ + c₂) := by
  simp [foldInst?, Option.bind_eq_some_iff]; grind

@[simp] theorem constFold.argsSet_foldInst : (foldInst acc i).argsSet ⊆ i.argsSet := by
  unfold foldInst; cases hi : foldInst? acc i <;> grind
grind_pattern constFold.argsSet_foldInst => (constFold.foldInst acc i).argsSet

@[simp, grind .] theorem constFold.results_foldInst : (foldInst acc i).results = i.results := by
  unfold foldInst; cases hi : foldInst? acc i <;> grind
@[simp, grind .] theorem constFold.resultsSet_foldInst : (foldInst acc i).resultsSet = i.resultsSet := by
  simp [Inst.resultsSet]

@[grind ←]
theorem constFold.wellFormed_foldInst :
    (acc.push i).toSeq.WellFormed ∅ → (acc.push <| foldInst acc i).toSeq.WellFormed ∅ := by
  grind

/--
Prove that a single step of the constant folder is sound.

This proof is still somewhat long, but it is *purely syntactical*.
Any semantic reasoning has already been done in
`Rewrite.isRefinedBy_of_contextual_isRefinedBy` and
in the proofs that the rewrites are (locally) sound.
-/
theorem constFold.foldInst_sound (wf : (acc.push i).toSeq.WellFormed ∅) :
    ⟦acc.push i⟧ {} ⊒ ⟦acc.push <| foldInst acc i⟧ {} := by
  have wf' : (acc.push <| foldInst acc i).toSeq.WellFormed ∅ := by grind
  unfold foldInst at *
  cases hi? : foldInst? acc i
  case none =>
    -- There was no match, thus `foldInst` was a no-op
    grind
  case some i' =>
    -- There *was* a match, so now we show that there is a context `C` and
    -- rewrite `rw` s.t. `(acc.push i).toSeq` is `C[rw.srw]` and
    -- `(acc.push i').toSeq` is `C[rw.tgt]`
    obtain ⟨x, y, z, hi, c₁, hy, c₂, hz, hi'⟩ : ∃ x y z,
          i = addOp x y z
          ∧ ∃ c₁, acc.matchConst y = some c₁
          ∧ ∃ c₂, acc.matchConst z = some c₂
          ∧ i' = constOp x (c₁ + c₂) := by
        simpa using hi?
    have wf' := by simpa only [hi?, Option.getD_some] using wf'
    simp only [Option.getD_some]

    -- We know that `x` cannot be the same variable as `y` nor `z`
    have : x ≠ y ∧ x ≠ z := by
      have hy : (addOp x y z).resultsSet.Disjoint (constOp y c₁).resultsSet := by grind
      have hz : (addOp x y z).resultsSet.Disjoint (constOp z c₂).resultsSet := by grind
      exact ⟨by simpa using hy, by simpa using hz⟩

    -- Consider whether the two arguments to the addition are the same or not,
    -- to determine which rewrite to instantiate, and how to construct the
    -- context to use as witness
    by_cases hyz : y = z
    case' pos =>
      obtain ⟨rfl, rfl⟩ : y = z ∧ c₁ = c₂ := by grind
      -- Since y = z, use the alternate rewrite, with a single constant
      let rw := constFoldRwAlt y x c₁
      -- Invoke the core theory's main result
      apply rw.isRefinedBy_of_contextual_isRefinedBy
      · exact constFoldRwAlt.isSound
      · grind
      · assumption

      -- The witness context:
      exists (acc.push i).toSeq.toContext [[y], [x]]
      and_intros
      · simp only [reduceCompleteToContext]
        and_intros; grind
        · exists constOp y c₁; grind
        · exists i; grind
      · rw [InstSeq.plug_toContext_eq_self_of]
        intro j hj idx hidx hres
        match idx with
        | 0 | 1 =>
          simpa using (by apply InstSeq.eq_of_results_eq _ hj <;> grind)
        | _+2 => contradiction

      · suffices (InstSeq.toContext [[y], [x]] acc.toSeq).plug rw.tgt = acc.toSeq by
          have toHole_i : i.toHole [[y], [x]] = .inr ⟨1, by grind⟩ := by
            rw [Inst.toHole_eq_inr_iff, hi]
            simp [List.idxOf?_eq_some_iff]
            grind
          simp [this, toHole_i, hi']
        rw [InstSeq.plug_toContext_eq_self_of]
        intro j hj idx hidx hres
        match idx with
        | 0 =>
          simpa using (by apply InstSeq.eq_of_results_eq _ hj <;> grind)
        | 1 =>
          exfalso
          have hjr : j.results = [x] := by grind
          have : i.resultsSet.Disjoint j.resultsSet := by grind
          simp [Inst.resultsSet, hjr, hi, VarSet.eq_empty_iff] at this
        | _+2 => contradiction


    case' neg =>
      -- Since y ≠ z, use the full rewrite
      let rw := constFoldRw y z x c₁ c₂
      -- Invoke the core theory's main result
      apply rw.isRefinedBy_of_contextual_isRefinedBy
      · exact constFoldRw.isSound
      · grind
      · assumption
      -- The witness context:
      exists (acc.push i).toSeq.toContext [[y], [z], [x]]
      and_intros
      · simp only [reduceCompleteToContext]
        refine ⟨by grind, ?_⟩
        and_intros
        · exists constOp y c₁; grind
        · exists constOp z c₂; grind
        · exists i; grind

      · rw [InstSeq.plug_toContext_eq_self_of]
        intro j hj idx hidx hres
        match idx with
        | 0 | 1 | 2 =>
          simpa using (by
            apply InstSeq.eq_of_results_eq _ hj
            <;> simp -failIfUnchanged <;> grind)
        | _+3 => contradiction

      · suffices (InstSeq.toContext [[y], [z], [x]] acc.toSeq).plug rw.tgt = acc.toSeq by
          have toHole_i : i.toHole [[y], [z], [x]] = .inr ⟨2, by grind⟩ := by
            simp only [Inst.toHole_eq_inr_iff]; grind
          simp [this, toHole_i, hi']
        rw [InstSeq.plug_toContext_eq_self_of]
        intro j hj idx hidx hres
        match idx with
        | 0 | 1 =>
          simpa using (by apply InstSeq.eq_of_results_eq _ hj <;> grind)
        | 2 =>
          exfalso
          have hjr : j.results = [x] := by grind
          have : i.resultsSet.Disjoint j.resultsSet := by grind
          simp [Inst.resultsSet, hjr, hi, VarSet.eq_empty_iff] at this
        | _+3 => contradiction

end FoldInstLemmas

/--
Prove that the constant folder is sound.
This is just a straightforward induction around `constFold.foldInst_sound`.
-/
theorem constFold_sound {is : Program}
    (wf : is.toSeq.WellFormed ∅) :
    ⟦is⟧ {} ⊒ ⟦constFold is⟧ {} := by
  let is := is.toSubarray
  suffices ∀ acc, (acc.toSeq ++ is.toSeq).WellFormed ∅ →
      ⟦acc.toSeq ++ is.toSeq⟧ {} ⊒ ⟦constFold.go acc is⟧ {} by
    specialize this .empty (by grind); simpa [is]
  clear wf
  intro acc
  fun_induction constFold.go acc is
  case case1 => grind
  case case2 acc is hsize i' ih =>
    intro wf
    suffices ⟦acc.toSeq ++ is.toSeq⟧ { } ⊒ ⟦(acc.push i').toSeq ++ is.popFront.toSeq⟧ { } by
      apply Refinement.trans this <| ih ?_
      grind
    suffices ⟦acc.push is[0]⟧ { } ⊒ ⟦acc.push i'⟧ { } by
      grind
    apply constFold.foldInst_sound
    · grind

#print axioms constFold_sound
