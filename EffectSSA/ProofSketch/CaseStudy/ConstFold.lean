module

public import EffectSSA.ProofSketch.ProofSketch
public import EffectSSA.ProofSketch.Rewrite
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
    suffices ⟦addOp z x y⟧ ρ ⊒ ⟦constOp z (c₁ + c₂)⟧ η by simpa [constFoldRw]
    replace h :
        let S := (constFoldRw x y z c₁ c₂).src
        S.EqnLemma x ρ
        ∧ S.EqnLemma y ρ := by
      simp [constFoldRw, Pattern.EqnLemmaUpTo] at h
      grind [constFoldRw]
    replace h :
        (constOp x c₁).EqnLemma x ρ
        ∧ (constOp y c₂).EqnLemma y ρ := by
      simp only [Pattern.EqnLemma] at h
      have := h.1 [constOp x c₁] (by simp [constFoldRw])
      have := h.2 [constOp y c₂] (by simp [constFoldRw])
      grind
    have hx : ρ.locals x = some c₁ := by grind [Inst.EqnLemma]
    have hy : ρ.locals y = some c₂ := by grind [Inst.EqnLemma]
    grind

@[simp, grind .]
axiom constFoldRwAlt.isSound : (constFoldRwAlt x z c₁).IsSound

/-! ## Implementation -/

structure RevInstSeq (ι) [SSA ι σ ν] where
  toList : List (Inst ι)

namespace RevInstSeq
variable [SSA ι σ ν]

def snoc (is : RevInstSeq ι) (i : Inst ι) : RevInstSeq ι :=
  ⟨i :: is.toList⟩

def toSeq (is : RevInstSeq ι) : InstSeq ι :=
  is.toList.reverse

section Lemmas

@[grind =, simp] theorem toSeq_nil : toSeq (⟨[]⟩ : RevInstSeq ι) = [] := by rfl
@[grind =, simp] theorem toSeq_snoc (is : RevInstSeq ι) (i : Inst ι) :
  toSeq (is.snoc i) = is.toSeq ++ [i] := by simp [snoc, toSeq]



end Lemmas
end RevInstSeq

/-! ### Matchers -/

/-- `is.matchConst x` returns `some n` if the instruction that defines
variable `x` in the (reverse) instruction sequence `is` is a
constant with value `n` (i.e, `constOp x n`). -/
def RevInstSeq.matchConst (is : RevInstSeq SimpleArith) (x : VarId) : Option Nat :=
  go is.toList
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

open RevInstSeq in
@[grind →]
theorem constOp_mem_of_matchConst_eq_some {acc : RevInstSeq SimpleArith} :
    acc.matchConst x = some c → constOp x c ∈ acc.toSeq := by
  rcases acc with ⟨is⟩
  simp only [matchConst, toSeq, List.mem_reverse]
  fun_induction matchConst.go x is <;> grind

/-! ### ConstFold -/

/--
`constFold is` returns an equivalent program, after a constant-folding pass.
-/
@[expose]
def constFold : InstSeq SimpleArith → InstSeq SimpleArith :=
  go ⟨[]⟩
where
  /--
  `foldInst? acc i` attempts to constant fold instruction `i` (referring to
  `acc` for the instructions that define `i`'s arguments), or returns `none`
  if `i` is not a well-formed, constant-foldable `add` instruction.
  -/
  foldInst? (acc : RevInstSeq SimpleArith) (i : Inst SimpleArith) : Option (Inst SimpleArith) := do
    let (x, y, z) ← matchAdd i
    let c₁ ← acc.matchConst y
    let c₂ ← acc.matchConst z
    return constOp x (c₁ + c₂)
  go (acc : RevInstSeq SimpleArith) : InstSeq SimpleArith → InstSeq SimpleArith
    | i :: is =>
        let i := (foldInst? acc i).getD i
        go (acc.snoc i) is
    | [] => acc.toSeq

@[simp, grind =]
theorem constFold.foldInst?_eq_some_iff :
    constFold.foldInst? acc i = some i' ↔ ∃ x y z,
      i = addOp x y z
      ∧ ∃ c₁, acc.matchConst y = some c₁
      ∧ ∃ c₂, acc.matchConst z = some c₂
      ∧ i' = constOp x (c₁ + c₂) := by
  simp [foldInst?, Option.bind_eq_some_iff]; grind

/--
Prove that the rewriter is sound.

This proof is still somewhat long, but it is *purely syntactical*.
Any semantic reasoning has already been done in
`Rewrite.isRefinedBy_of_contextual_isRefinedBy` and
in the proofs that the rewrites are (locally) sound.
-/
theorem constFold_sound (wf : is.WellFormed ∅) :
    ⟦is⟧ {} ⊒ ⟦constFold is⟧ {} := by
  suffices ∀ acc, (acc.toSeq ++ is).WellFormed ∅ →
      ⟦acc.toSeq ++ is⟧ {} ⊒ ⟦constFold.go acc is⟧ {} by
    specialize this ⟨[]⟩ wf; simpa
  clear wf
  induction is
  case nil => grind [constFold.go]
  case cons i is ih =>
    intro acc wf
    let i? := constFold.foldInst? acc i
    let i' := i?.getD i
    suffices ⟦ (acc.snoc i).toSeq ++ is ⟧ {} ⊒ ⟦ constFold.go (acc.snoc i') is ⟧ {} by
      simpa
    cases hi : i?
    case none =>
      -- There was no match, thus `i'` and `i` are actually equal
      grind
    case some j =>
      -- There *was* a match, so now we show that there is a context `C` and
      -- rewrite `rw` s.t. `(acc.snoc i).toSeq` is `C[rw.srw]` and
      -- `(acc.snoc i').toSeq` is `C[rw.tgt]`
      obtain rfl : i' = j := by grind
      obtain ⟨x, y, z, hi, c₁, hy, c₂, hz, hi'⟩ : ∃ x y z,
          i = addOp x y z
          ∧ ∃ c₁, acc.matchConst y = some c₁
          ∧ ∃ c₂, acc.matchConst z = some c₂
          ∧ i' = constOp x (c₁ + c₂) := by
        simpa [i?] using hi

      generalize hjs : (acc.snoc i).toSeq = js
      -- The next accumulator is still well-formed
      generalize hacc' : acc.snoc i' = acc'
      have wf_acc' : acc'.toSeq.WellFormed ∅ := by
        simp_all [← hacc']
      specialize ih acc' <| by
        suffices acc'.toSeq.results = acc.toSeq.results ∪ i.resultsSet by grind
        simp [← hacc', hi, hi']

      suffices ⟦ js ⟧ {} ⊒ ⟦ acc'.toSeq ⟧ {} by
        apply Refinement.trans ?_ ih; grind

      -- It suffices to show the constant-folder is equivalent to a local rewrite
      have : x ≠ y := by
        have : (addOp x y z).resultsSet.Disjoint (constOp y c₁).resultsSet := by grind
        simpa
      have : x ≠ z := by
        have : (addOp x y z).resultsSet.Disjoint (constOp z c₂).resultsSet := by grind
        simpa
      by_cases hyz : y = z
      case' pos =>
        subst hyz
        obtain rfl : c₁ = c₂ := by grind
        let rw := constFoldRwAlt y x c₁
        apply rw.isRefinedBy_of_contextual_isRefinedBy
        · exact constFoldRwAlt.isSound
        · grind
        · assumption

        -- The witness context:
        exists js.toContext [[y], [x]]
        and_intros
        · rw [InstSeq.complete_toContext_iff [[y], [x]]]
          and_intros; grind
          · intro x' hx'
            if x' = [x] then
              exists i; grind
            else if x' = [y] then
              exists constOp y c₁; grind
            else
              grind
        · subst js
          rw [InstSeq.plug_toContext_eq_self_of ([[y], [x]])]
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
            simp [← hacc', ← hjs, this, toHole_i, hi']
          rw [InstSeq.plug_toContext_eq_self_of ([[y], [x]])]
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
        replace hyz : y ≠ z := hyz
        -- Since y ≠ z, we use the full rewrite
        let rw := constFoldRw y z x c₁ c₂
        apply rw.isRefinedBy_of_contextual_isRefinedBy
        · exact constFoldRw.isSound
        · grind
        · assumption
        -- The witness context:
        let xyz := [[y], [z], [x]]
        exists js.toContext xyz
        and_intros
        · rw [InstSeq.complete_toContext_iff xyz]
          and_intros
          · simp [xyz]; grind
          · intro x' hx'
            if x' = [x] then
              exists i; grind
            else if x' = [y] then
              exists constOp y c₁; grind
            else if x' = [z] then
              exists constOp z c₂; grind
            else
              grind

        · rw [InstSeq.plug_toContext_eq_self_of xyz]
          intro j hj idx hidx hres
          subst xyz hacc' hjs
          match idx with
          | 0 | 1 | 2 =>
            simpa using (by
              apply InstSeq.eq_of_results_eq _ hj
              <;> simp -failIfUnchanged <;> grind)
          | _+3 => contradiction

        · suffices (InstSeq.toContext xyz acc.toSeq).plug rw.tgt = acc.toSeq by
            have toHole_i : i.toHole xyz = .inr ⟨2, by grind⟩ := by
              simp only [Inst.toHole_eq_inr_iff]; grind
            simp [← hacc', ← hjs, this, toHole_i, hi']
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

#print axioms constFold_sound
